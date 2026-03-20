//! Pass that takes a blockless dag and calculates liveness information for each node.
//!
//! TODO: I think there is a way to merge this pass with register allocation, by using
//! the same bottom-up algorithm used in wom::flattening::allocate_registers, keeping
//! track of the state independently for each execution path.

use std::collections::{BTreeMap, HashMap};

use crate::{
    loader::{
        blockless_dag::{GenericBlocklessDag, GenericNode, GenericNode as BDNode},
        dag::{NodeInput, ValueOrigin},
        passes::{
            blockless_dag::{BlocklessDag, BreakTarget, TargetType},
            calc_input_redirection::Redirection,
        },
    },
    utils::rev_vec_filler::RevVecFiller,
};

#[derive(Debug)]
pub struct Liveness {
    /// For each value origin, holds the ranges where the value is live.
    ///
    /// The liveness may be intermitent, because in some execution paths the
    /// value can be dropped earlier than in others. If a value is not live in some
    /// range after its origin, it is guaranteed it won't be needed again in every
    /// possible execution path from that range.
    ///
    /// The ranges are non-overlapping and sorted. Each node index in a range is a
    /// node where the value is available for reading, so the range starts one node
    /// after the origin, and ends at the last node that uses the value.
    live_ranges: HashMap<ValueOrigin, Vec<(usize, usize)>>,

    /// The set of outputs indexed from the Input node that are redirected
    /// as-is to the next iteration of the loop.
    ///
    /// The vector is sorted, and contains no duplicates.
    ///
    /// This is useful to detect outer values that are read by the loop, but
    /// not written, so they can be preserved across the entire loop execution,
    /// eliding unnecessary copies.
    ///
    /// On the toplevel block (which is not a loop), this is always empty.
    redirected_inputs: Vec<u32>,
}

impl Liveness {
    /// Query the liveness information for a given node output.
    ///
    /// Returns the index of the last node that uses the output, if known,
    /// otherwise it is already dead, and returns the index of the node that
    /// produced the output.
    ///
    /// TODO: see if it is better to return an enum {Alive, Dead, LastUsageIsNow}.
    pub fn query_liveness(&self, curr_node_idx: usize, origin: &ValueOrigin) -> usize {
        // The first range whose current node index greater or equal to its start.
        let interval_idx = self
            .last_usage_map
            .partition_point(|(interval_start, _)| curr_node_idx < *interval_start);
        let last_usage = &self.last_usage_map[interval_idx].1;
        last_usage.get(origin).cloned().unwrap_or(origin.node)
    }

    pub fn query_if_input_is_redirected(&self, input_idx: u32) -> bool {
        self.redirected_inputs.binary_search(&input_idx).is_ok()
    }
}

pub type LivenessDag<'a> = GenericBlocklessDag<'a, Liveness>;

pub type Node<'a> = GenericNode<'a, Liveness>;

impl<'a> LivenessDag<'a> {
    pub fn from_blockless_dag(dag: BlocklessDag<'a>) -> Self {
        use crate::loader::passes::blockless_dag::Operation::*;

        let nodes = dag.nodes;

        let mut last_usage = BTreeMap::new();
        let mut liveness_nodes: RevVecFiller<Node<'a>> = RevVecFiller::new(nodes.len());

        // For each node interval, holds a map of the last usage of a value produced
        // by some node (that might be outside the current interval). If not present,
        // the value was already dead before the interval.
        //
        // The intervals are delimited by labels and breaks, so the liveness
        // might change suddenly from one interval to the next.
        //
        // This vec is sorted in decreasing order of the intervals, and the tuple is:
        // (index of the first node in the interval, map of origin to last usage).
        // E.g., if there are 15 nodes, the order of the elements might be [(10, _),(5, _),(0, _)].
        let mut last_usage_map = Vec::new();

        let mut usage_idx_for_label = HashMap::new();

        for (
            index,
            BDNode {
                operation,
                inputs,
                output_types,
            },
        ) in nodes.into_iter().enumerate().rev()
        {
            // Process subnodes recursively
            let operation = {
                match operation {
                    Loop {
                        sub_dag,
                        break_targets,
                    } => {
                        let sub_dag = LivenessDag::from_blockless_dag(sub_dag);

                        Loop {
                            sub_dag,
                            break_targets,
                        }
                    }

                    // We need to break the ranges at labels and breaks.
                    Label { id } => {
                        // On a label we finish the previous range.
                        usage_idx_for_label.insert(id, last_usage_map.len());
                        last_usage_map.push((index, std::mem::take(&mut last_usage)));
                        Label { id }
                    }
                    Br(break_target) => {
                        // On a break, we discard the previous range and start a new one
                        // using the target as basis (if local).
                        last_usage = BTreeMap::new();
                        if break_target.depth == 0
                            && let TargetType::Label(label_id) = break_target.kind
                        {
                            let target_range_idx = usage_idx_for_label[&label_id];
                            merge_usages(
                                &mut last_usage,
                                &last_usage_map[target_range_idx].1,
                                index,
                            );
                        }
                        Br(break_target)
                    }
                    BrIf(break_target) => {
                        cond_break(
                            &break_target,
                            index,
                            &mut last_usage,
                            &mut last_usage_map,
                            &mut usage_idx_for_label,
                        );
                        BrIf(break_target)
                    }
                    BrIfZero(break_target) => {
                        cond_break(
                            &break_target,
                            index,
                            &mut last_usage,
                            &mut last_usage_map,
                            &mut usage_idx_for_label,
                        );
                        BrIfZero(break_target)
                    }
                    BrTable { targets } => {
                        // BrTable is similar to Br that we discard the current range,
                        // but similar to BrIf and BrIfZero that we merge all the target
                        // together.
                        last_usage = BTreeMap::new();
                        for break_target in &targets {
                            if break_target.target.depth == 0
                                && let TargetType::Label(label_id) = break_target.target.kind
                            {
                                merge_usages(
                                    &mut last_usage,
                                    &last_usage_map[usage_idx_for_label[&label_id]].1,
                                    index,
                                );
                            }
                        }

                        BrTable { targets }
                    }

                    // Other operations remain unchanged, but we have to spell them out
                    // because the types are different.
                    Inputs => Inputs,
                    WASMOp(operator) => WASMOp(operator),
                }
            };

            // For each input, we mark its last used node as the current node index, if it is not already marked.
            for input in &inputs {
                if let NodeInput::Reference(origin) = input {
                    last_usage.entry(*origin).or_insert(index);
                }
            }

            liveness_nodes
                .try_push_front(Node {
                    operation,
                    inputs,
                    output_types,
                })
                .unwrap();
        }

        last_usage_map.push((0, last_usage));

        // Use last usage map to build the live ranges for each value origin.
        let mut live_ranges = HashMap::new();
        while let Some((interval_start, usage_map)) = last_usage_map.pop() {
            for (origin, last_usage) in usage_map {
                let start = interval_start.max(origin.node + 1);
                let end = if let Some((next_interval_start, _)) = last_usage_map.last() {
                    last_usage.min(*next_interval_start - 1)
                } else {
                    last_usage
                };
                let ranges: &mut Vec<(usize, usize)> = live_ranges.entry(origin).or_default();

                if let Some((_, prev_range_end)) = ranges.last_mut()
                    && *prev_range_end == start
                {
                    // Merge with the previous range if they are contiguous.
                    *prev_range_end = end;
                } else {
                    // Add a new range otherwise.
                    ranges.push((start, end));
                }
            }
        }

        let redirections = dag.block_data;
        let redirected_inputs = redirections
            .into_iter()
            .enumerate()
            .filter_map(|(idx, redir)| {
                (redir == Redirection::FromInput(idx as u32)).then_some(idx as u32)
            })
            .collect();

        LivenessDag {
            nodes: liveness_nodes.try_into_vec().unwrap(),
            block_data: Liveness {
                live_ranges,
                redirected_inputs,
            },
        }
    }
}

fn cond_break(
    break_target: &BreakTarget,
    node_idx: usize,
    last_usage: &mut BTreeMap<ValueOrigin, usize>,
    last_usage_map: &mut Vec<(usize, BTreeMap<ValueOrigin, usize>)>,
    usage_idx_for_label: &mut HashMap<u32, usize>,
) {
    // If the target is local, we finish the previous range, and start a new
    // one merging the current state with the one saved at the target label.
    //
    // Otherwise, just return and don't change the current range.
    if break_target.depth != 0 {
        return;
    }
    let TargetType::Label(label_id) = break_target.kind else {
        return;
    };

    let mut merged = BTreeMap::new();
    merge_usages(
        &mut merged,
        &last_usage_map[usage_idx_for_label[&label_id]].1,
        node_idx,
    );
    merge_usages(&mut merged, last_usage, node_idx);

    usage_idx_for_label.insert(label_id, last_usage_map.len());
    last_usage_map.push((node_idx + 1, std::mem::replace(last_usage, merged)));
}

fn merge_usages(
    target: &mut BTreeMap<ValueOrigin, usize>,
    source: &BTreeMap<ValueOrigin, usize>,
    end_range_idx: usize,
) {
    // Discard values originating after the end of the range.
    let upper_bound = ValueOrigin {
        node: end_range_idx + 1,
        output_idx: 0,
    };
    for (origin, usage) in source.range(..upper_bound) {
        target
            .entry(*origin)
            .and_modify(|u| *u = (*u).max(*usage))
            .or_insert(*usage);
    }
}
