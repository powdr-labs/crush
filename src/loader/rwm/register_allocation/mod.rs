mod occupation_tracker;

use std::{
    collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, VecDeque},
    num::NonZeroU32,
    ops::Range,
};

use wasmparser::{Operator as Op, ValType};

use crate::{
    loader::{
        Module,
        blockless_dag::{BreakTarget, GenericBlocklessDag, NodeInput, Operation, TargetType},
        dag::ValueOrigin,
        passes::blockless_dag::GenericNode,
        rwm::{
            liveness_dag::{self, LivenessDag, single_range},
            register_allocation::occupation_tracker::{Occupation, OccupationTracker},
        },
        settings::Settings,
        word_count_type, word_count_types,
    },
    utils::rev_vec_filler::RevVecFiller,
};

#[derive(Debug)]
pub enum Error {
    NotAllocated,
    NotARegister,
}

/// One possible register allocation for a given DAG.
#[derive(Debug)]
pub struct Allocation {
    /// The registers assigned to the nodes outputs.
    nodes_outputs: BTreeMap<ValueOrigin, Range<u32>>,
    /// The full register occupation map.
    occupation: Occupation,
    /// The map of label id to its node index, for quick lookup on a break.
    pub labels: HashMap<u32, usize>,
    /// The call frame start register for each call node index.
    pub call_frames: HashMap<usize, u32>,
}

impl Allocation {
    pub fn get_for_node(&self, node_index: usize) -> impl Iterator<Item = Range<u32>> {
        let start = ValueOrigin {
            node: node_index,
            output_idx: 0,
        };
        let end = ValueOrigin {
            node: node_index + 1,
            output_idx: 0,
        };
        self.nodes_outputs.range(start..end).map(|(_, r)| r.clone())
    }

    pub fn get(&self, origin: &ValueOrigin) -> Result<Range<u32>, Error> {
        self.nodes_outputs
            .get(origin)
            .cloned()
            .ok_or(Error::NotAllocated)
    }

    pub fn get_as_reg(&self, input: &NodeInput) -> Result<Range<u32>, Error> {
        match input {
            NodeInput::Reference(origin) => self.get(origin),
            NodeInput::Constant(_) => {
                // Constants don't need register allocation
                Err(Error::NotARegister)
            }
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&ValueOrigin, &Range<u32>)> {
        self.nodes_outputs.iter()
    }

    /// Returns all the occupied register ranges crossing a single node index.
    ///
    /// Does not include the inputs of the node, but includes its outputs, because the
    /// live range of an output is [A, B) where A is the node prducing it and B is the
    /// last node consuming it.
    pub fn occupation_for_node(&self, node_index: usize) -> Vec<Range<u32>> {
        self.occupation
            .reg_occupation(&single_range(node_index..(node_index + 1)))
    }

    /// Precomputes a map from node index to registers that should be dropped after that node.
    pub fn per_node_occupation(&self) -> PerNodeOccupation {
        self.occupation.per_node_tracker()
    }

    /// Returns `true` if the value at `origin` is read by at least one node.
    ///
    /// In the dimensionless-ranges convention, an unused value has an empty
    /// live range `[X, X)` while a used value has at least one non-empty range,
    /// so this is decidable from the stored live ranges alone — even when the
    /// unique consumer is the immediately following node, which the
    /// `occupation_for_node` queries cannot see (its live range ends before
    /// that query point).
    pub fn is_value_used(&self, origin: &ValueOrigin) -> bool {
        self.occupation.is_value_used(*origin)
    }
}

pub type AllocatedDag<'a> = GenericBlocklessDag<'a, Allocation>;
pub type Node<'a> = GenericNode<'a, Allocation>;

/// Struct to track every live chunk independently.
///
/// It compares by reverse live range end so it can be inserted in a BinaryHeap
/// to efficiently track the currently alive chunks by their end point.
#[derive(Eq)]
pub struct RangeReg {
    pub live: Range<usize>,
    pub regs: Range<u32>,
}
impl PartialEq for RangeReg {
    fn eq(&self, other: &Self) -> bool {
        self.live.end == other.live.end
    }
}
impl PartialOrd for RangeReg {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for RangeReg {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Reverse order: think of higer as "first to die".
        other.live.end.cmp(&self.live.end)
    }
}

/// This is a tracker that reply the allocation state per node, and
/// can be used to detect when a value is no longer alive and its
/// register can be dropped.
pub struct PerNodeOccupation {
    next_node: usize,
    /// The allocations that have not yet become alive, sorted by their live
    /// range start in reverse order (so we can pop to get the next allocation).
    rev_sorted_next_allocs: Vec<RangeReg>,
    active_allocs: BinaryHeap<RangeReg>,
}

pub struct NodeRegChanges {
    pub node_index: usize,
    pub dying: BTreeSet<u32>,
    pub ephemeral: Vec<u32>,
    pub newly_live: Vec<u32>,
}

impl PerNodeOccupation {
    /// Advances the tracker to the next node, returning the set of registers that
    /// are just dying at this node. To get what actually must be dropped, make
    /// the difference with the registers that are alive at this node (which doesn't
    /// include the dying, but includes the ones just becoming live).
    pub fn advance(&mut self) -> NodeRegChanges {
        let node_index = self.next_node;
        self.next_node += 1;

        // Remove the dying allocations and collect their registers.
        let mut dying = BTreeSet::new();
        while let Some(next_to_die) = self.active_allocs.peek()
            && next_to_die.live.end <= node_index
        {
            for reg in next_to_die.regs.clone() {
                dying.insert(reg);
            }
            self.active_allocs.pop();
        }

        // Add the new allocations.
        let mut ephemeral = Vec::new();
        let mut newly_live = Vec::new();
        while let Some(next_to_live) = self.rev_sorted_next_allocs.last()
            && next_to_live.live.start <= node_index
        {
            let next_to_live = self.rev_sorted_next_allocs.pop().unwrap();
            if next_to_live.live.end == node_index {
                // This is an ephemeral value that must be discarded right away
                for reg in next_to_live.regs {
                    ephemeral.push(reg);
                }
            } else {
                for reg in next_to_live.regs.clone() {
                    newly_live.push(reg);
                }
                self.active_allocs.push(next_to_live);
            }
        }

        NodeRegChanges {
            node_index,
            dying,
            ephemeral,
            newly_live,
        }
    }

    pub fn active(&self) -> impl Iterator<Item = &RangeReg> {
        self.active_allocs.iter()
    }
}

struct OptimisticAllocator {
    occupation_tracker: OccupationTracker,
    labels: HashMap<u32, usize>,
}

impl OptimisticAllocator {
    /// Allocates the inputs of a node that have not been allocated yet.
    fn allocate_inputs<'a, S: Settings>(
        &mut self,
        inputs: &[NodeInput],
        nodes: &[liveness_dag::Node<'a>],
    ) {
        for input in inputs {
            if let NodeInput::Reference(origin) = input {
                self.occupation_tracker
                    .try_allocate(*origin, assert_non_zero(word_count::<S>(nodes, *origin)));
            }
        }
    }

    /// Allocates the outputs of a node that have not been allocated yet.
    fn allocate_outputs<S: Settings>(&mut self, node_index: usize, output_types: &[ValType]) {
        for (output_idx, output_type) in output_types.iter().enumerate() {
            let origin = ValueOrigin {
                node: node_index,
                output_idx: output_idx as u32,
            };
            let num_words = assert_non_zero(word_count_type::<S>(*output_type));
            self.occupation_tracker.try_allocate(origin, num_words);
        }
    }
}

/// Allocates the inputs for a break node.
fn handle_break<'a, S: Settings>(
    nodes: &[liveness_dag::Node<'a>],
    oa: &mut VecDeque<OptimisticAllocator>,
    inputs: &[NodeInput],
    break_target: &BreakTarget,
    is_conditional: bool,
) -> usize {
    // For conditional breaks, the last input is the condition,
    // which is not tied to the break target.
    let inputs = if is_conditional {
        let (break_inputs, condition) = inputs.split_at(inputs.len() - 1);
        oa[0].allocate_inputs::<S>(condition, nodes);
        break_inputs
    } else {
        inputs
    };

    let mut number_of_saved_copies = 0;

    let curr_depth = oa.len() as u32 - 1;
    match break_target.kind {
        TargetType::Function => {
            // This is a function return. We must try to place the outputs in the expected registers
            // for function return.
            assert!(break_target.depth == curr_depth);
            let mut next_reg = 0u32;
            for input in inputs {
                let origin = unwrap_ref(input, "break inputs must be references");
                let num_words = word_count::<S>(nodes, *origin);
                if try_allocate_with_hint(oa, *origin, next_reg..next_reg + num_words) {
                    number_of_saved_copies += num_words as usize;
                }
                next_reg += num_words;
            }
        }
        TargetType::Loop => {
            // This is a break to a loop iteration.

            // For each input, we try to mirror the allocation expected by the loop input.
            let target_idx = break_target.depth as usize;
            for (input_index, break_input) in inputs.iter().enumerate() {
                let loop_input_origin = ValueOrigin {
                    // Node 0 is always the input node of a block.
                    node: 0,
                    output_idx: input_index as u32,
                };
                let loop_input_allocation = oa[target_idx]
                    .occupation_tracker
                    .get_allocation(loop_input_origin)
                    .expect("loop input must be allocated");
                let num_words = loop_input_allocation.len();
                let break_origin = unwrap_ref(break_input, "break inputs must be references");

                if try_allocate_with_hint(oa, *break_origin, loop_input_allocation) {
                    number_of_saved_copies += num_words;
                }
            }
        }
        TargetType::Label(label) => {
            // Try to allocate the break input at the same registers as the label output.

            // We are dealing with potentially two different levels of depth here,
            // target_idx is the level that contains the label with the outputs we
            // want to match. 0 is the current level we must set the allocations for.
            //
            // They might be the same, but not necessarily.
            let target_idx = break_target.depth as usize;

            // Node index at the target level
            let label_index = *oa[target_idx]
                .labels
                .get(&label)
                .expect("label must be defined");

            for (index, break_input) in inputs.iter().enumerate() {
                let label_origin = ValueOrigin {
                    node: label_index,
                    output_idx: index as u32,
                };
                let label_allocation = oa[target_idx]
                    .occupation_tracker
                    .get_allocation(label_origin)
                    .unwrap();
                let num_words = label_allocation.len();

                // Value origin at the current level we are setting the allocation for.
                let break_origin = unwrap_ref(break_input, "break inputs must be references");

                if try_allocate_with_hint(oa, *break_origin, label_allocation) {
                    number_of_saved_copies += num_words;
                }
            }
        }
    }

    number_of_saved_copies
}

fn recursive_block_allocation<'a, S: Settings>(
    prog: &Module<'a>,
    mut nodes: Vec<liveness_dag::Node<'a>>,
    oa: &mut VecDeque<OptimisticAllocator>,
) -> (Vec<Node<'a>>, usize) {
    let mut number_of_saved_copies = 0;

    let mut new_nodes = RevVecFiller::new(nodes.len());

    for index in (0..nodes.len()).rev() {
        let node = nodes.pop().unwrap();

        let operation = match node.operation {
            Operation::Inputs => {
                assert_eq!(index, 0);
                // All node outputs must have been allocated already.
                Operation::Inputs
            }
            Operation::WASMOp(operator) => {
                match &operator {
                    Op::Call { .. } | Op::CallIndirect { .. } => 'call_match: {
                        let inputs = if let Op::Call { function_index } = &operator {
                            // If this is an imported function, treat it as a generic operation.
                            // We assume imported functions are kinda like system calls, and can
                            // read and write to any register we choose here.
                            if prog.get_imported_func(*function_index).is_some() {
                                oa[0].allocate_inputs::<S>(&node.inputs, &nodes);
                                oa[0].allocate_outputs::<S>(index, &node.output_types);
                                break 'call_match;
                            }
                            &node.inputs
                        } else {
                            // This is an indirect call, we need allocate the last input separately.
                            let (fn_inputs, fn_index) = node.inputs.split_at(node.inputs.len() - 1);
                            oa[0].allocate_inputs::<S>(fn_index, &nodes);
                            fn_inputs
                        };

                        // On a given node index, the one after the last used slot is the
                        // start of the called function frame. From there, two slots are
                        // reserved for return address and frame pointer, and then come
                        // the arguments.
                        let output_sizes =
                            node.output_types.iter().map(|ty| word_count_type::<S>(*ty));
                        let mut next_arg = oa[0].occupation_tracker.allocate_fn_call(
                            index,
                            output_sizes,
                            &mut number_of_saved_copies,
                        );

                        // Try to place the function inputs at the expected argument slots.
                        for input in inputs {
                            let origin =
                                unwrap_ref(input, "function call inputs must be references");
                            let num_words = word_count::<S>(&nodes, *origin);
                            if try_allocate_with_hint(oa, *origin, next_arg..next_arg + num_words) {
                                number_of_saved_copies += num_words as usize;
                            }
                            next_arg += num_words;
                        }
                    }
                    _ => {
                        // This is the general case. Allocates inputs and outputs that have not been allocated yet.
                        oa[0].allocate_inputs::<S>(&node.inputs, &nodes);
                        oa[0].allocate_outputs::<S>(index, &node.output_types);
                    }
                };

                Operation::WASMOp(operator)
            }
            Operation::Label { id } => {
                // Record the current allocation for this label
                oa[0].labels.insert(id, index);

                // Allocate any remaining output that was not allocated yet.
                oa[0].allocate_outputs::<S>(index, &node.output_types);

                Operation::Label { id }
            }
            Operation::Loop {
                sub_dag,
                break_targets,
            } => {
                // As with the general case, we allocate the inputs of the loop node.
                // It has no outputs that would require allocation.
                oa[0].allocate_inputs::<S>(&node.inputs, &nodes);

                // We need a new allocation tracker for the loop body.
                // It is derived from the current one, completely blocking the
                // slots that are occupied for the duration of the loop.
                let LivenessDag {
                    nodes: loop_nodes,
                    block_data: loop_liveness,
                } = sub_dag;
                let mut occupation_tracker = oa[0]
                    .occupation_tracker
                    .make_sub_tracker(index, loop_liveness);

                // There is an heuristic we do here to minimize copies: for each loop input, if this
                // is the last usage of the value, or if the loop body does not change the input and just
                // forwards it unchanged to the next iteration, we can fix the allocation of the input to
                // the current one, saving a copy.
                for (input_idx, input) in node.inputs.iter().enumerate() {
                    let origin = unwrap_ref(input, "loop inputs must be references");

                    // Check if we can fix this allocation for the loop input.
                    // Find the range that either contains the loop node or ends at it.
                    let value_liveness = oa[0].occupation_tracker.liveness().query_liveness(origin);
                    let err_msg = "liveness bug: value used outside of its live ranges";
                    let pos = value_liveness.partition_point(|r| r.start <= index);
                    assert!(pos > 0, "{}", err_msg);
                    let relevant_range = &value_liveness[pos - 1];
                    assert!(relevant_range.end >= index, "{}", err_msg);
                    let alloc_fixed = if relevant_range.end == index {
                        // The range covering the loop node ends exactly here, so
                        // on this execution path the loop consumes the value.
                        // Try to reuse the same register for the loop input.
                        // Doesn't always work, because the same input value could be used
                        // by multiple loop inputs. Only one will be able to reuse the allocation.
                        let allocation = oa[0].occupation_tracker.get_allocation(*origin).unwrap();
                        let alloc_len = allocation.len();
                        let hint_used = occupation_tracker.try_allocate_with_hint(
                            ValueOrigin {
                                node: 0,
                                output_idx: input_idx as u32,
                            },
                            allocation,
                        );

                        if hint_used {
                            number_of_saved_copies += alloc_len;
                        }
                        hint_used
                    } else if occupation_tracker
                        .liveness()
                        .query_if_input_is_redirected(input_idx as u32)
                    {
                        // This input outlives the loop body, but inside the loop
                        // it is just forwarded unchanged to the next iteration.
                        // We can always reuse the allocation from the outer level.
                        let allocation = oa[0].occupation_tracker.get_allocation(*origin).unwrap();
                        number_of_saved_copies += allocation.len();

                        occupation_tracker.set_allocation(
                            ValueOrigin {
                                node: 0,
                                output_idx: input_idx as u32,
                            },
                            allocation,
                        );
                        true
                    } else {
                        false
                    };

                    // If this input was used to save a copy here, it can't be improved upon
                    // without reprocessing the loop. We mark it as fixed, in case it came
                    // from a function call, so that it won't be considered for output relocation
                    // at the call node.
                    if alloc_fixed {
                        oa[0].occupation_tracker.mark_as_fixed(origin);
                    }
                }

                let mut loop_oa = OptimisticAllocator {
                    occupation_tracker,
                    labels: HashMap::new(),
                };

                // Allocate the rest of the input node values (inside the loop body).
                loop_oa.allocate_outputs::<S>(0, &loop_nodes[0].output_types);
                oa.push_front(loop_oa);

                let (loop_nodes, loop_saved_copies) =
                    recursive_block_allocation::<S>(prog, loop_nodes, oa);

                // Pop the loop allocation tracker.
                let OptimisticAllocator {
                    occupation_tracker,
                    labels,
                    ..
                } = oa.pop_front().unwrap();

                // Project the allocations back to the outer level. This will prevent
                // the outer level from placing allocations that should survive across
                // this loop block on registers that could be overwritten here.
                oa[0]
                    .occupation_tracker
                    .project_from_sub_tracker(index, &occupation_tracker);

                let allocation = occupation_tracker.into_allocations(labels);

                // Collect the new nodes
                let loop_dag = AllocatedDag {
                    nodes: loop_nodes,
                    block_data: allocation,
                };

                number_of_saved_copies += loop_saved_copies;

                Operation::Loop {
                    sub_dag: loop_dag,
                    break_targets,
                }
            }
            Operation::Br(break_target) => {
                number_of_saved_copies +=
                    handle_break::<S>(&nodes, oa, &node.inputs, &break_target, false);
                Operation::Br(break_target)
            }
            Operation::BrIf(break_target) => {
                number_of_saved_copies +=
                    handle_break::<S>(&nodes, oa, &node.inputs, &break_target, true);
                Operation::BrIf(break_target)
            }
            Operation::BrIfZero(break_target) => {
                number_of_saved_copies +=
                    handle_break::<S>(&nodes, oa, &node.inputs, &break_target, true);
                Operation::BrIfZero(break_target)
            }
            Operation::BrTable { targets } => {
                let mut inputs = Vec::new();
                for target in &targets {
                    inputs.clear();
                    inputs.extend(
                        target
                            .input_permutation
                            .iter()
                            .map(|&idx| node.inputs[idx as usize].clone()),
                    );
                    number_of_saved_copies +=
                        handle_break::<S>(&nodes, oa, &inputs, &target.target, false);
                }
                // Allocate the selector input
                let selector_input = &node.inputs[node.inputs.len() - 1..];
                oa[0].allocate_inputs::<S>(selector_input, &nodes);

                Operation::BrTable { targets }
            }
        };

        let new_node = Node {
            operation,
            inputs: node.inputs,
            output_types: node.output_types,
        };

        new_nodes.try_push_front(new_node).unwrap();
    }

    (new_nodes.try_into_vec().unwrap(), number_of_saved_copies)
}

fn try_allocate_with_hint(
    oa: &mut VecDeque<OptimisticAllocator>,
    origin: ValueOrigin,
    hint: Range<u32>,
) -> bool {
    oa[0]
        .occupation_tracker
        .try_allocate_with_hint(origin, hint)
}

/// Allocates registers for a given function DAG. It is not optimal, but it tries
/// to minimize the number of copies and used registers.
///
/// Does the allocation bottom up, following the execution paths independently,
/// proposing register assignment for future nodes (so to avoid copies), but
/// leaving a final assignment for the traversed nodes.
pub fn optimistic_allocation<'a, S: Settings>(
    prog: &Module<'a>,
    func_idx: u32,
    dag: LivenessDag<'a>,
) -> (AllocatedDag<'a>, usize) {
    let LivenessDag {
        nodes,
        block_data: liveness,
    } = dag;

    let mut oa = OptimisticAllocator {
        occupation_tracker: OccupationTracker::new(liveness),
        labels: HashMap::new(),
    };

    // Fix the allocation of the function inputs first
    let inputs = &nodes[0];
    let Operation::Inputs = &inputs.operation else {
        panic!("First node must be Inputs");
    };
    let mut next_in_reg = 0u32;
    for (output_idx, input) in inputs.output_types.iter().enumerate() {
        let origin = ValueOrigin {
            node: 0,
            output_idx: output_idx as u32,
        };
        let num_words = word_count_type::<S>(*input);
        oa.occupation_tracker
            .set_allocation(origin, next_in_reg..next_in_reg + num_words);
        next_in_reg += num_words;
    }

    // Calculate the space needed for the return values.
    let outputs = prog.get_func_type(func_idx).ty.results();
    let out_words = word_count_types::<S>(outputs);

    // Reserve the space for the return address and frame pointer after the maximum
    // between the inputs and outputs.
    let ra_fp_regs = next_in_reg.max(out_words);
    oa.occupation_tracker
        .reserve_range(ra_fp_regs..ra_fp_regs + 2 * S::words_per_ptr());

    // Do the allocation for the rest of the nodes, bottom up.
    let mut oa_stack = VecDeque::from([oa]);
    let (nodes, number_of_saved_copies) =
        recursive_block_allocation::<S>(prog, nodes, &mut oa_stack);

    // Generate the final allocation for this block
    let OptimisticAllocator {
        occupation_tracker,
        labels,
        ..
    } = oa_stack.pop_front().unwrap();

    let allocation = occupation_tracker.into_allocations(labels);

    (
        AllocatedDag {
            nodes,
            block_data: allocation,
        },
        number_of_saved_copies,
    )
}

/// Helper to extract ValueOrigin from NodeInput
fn unwrap_ref<'a>(input: &'a NodeInput, msg: &'static str) -> &'a ValueOrigin {
    match input {
        NodeInput::Reference(origin) => origin,
        NodeInput::Constant(_) => panic!("{}", msg),
    }
}

/// Gets the type of a value origin
fn type_of<'a>(nodes: &[liveness_dag::Node<'a>], origin: ValueOrigin) -> ValType {
    let node = &nodes[origin.node];
    node.output_types[origin.output_idx as usize]
}

fn assert_non_zero(value: u32) -> NonZeroU32 {
    NonZeroU32::new(value).expect("word count is non-zero")
}

/// Gets the word count of a value origin
fn word_count<'a, S: Settings>(nodes: &[liveness_dag::Node<'a>], origin: ValueOrigin) -> u32 {
    word_count_type::<S>(type_of(nodes, origin))
}
