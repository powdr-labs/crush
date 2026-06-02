//! This module flattens the DAG structure, generating an assembly-like representation.
//!
//! The algorithm is straightforward and linear, as most of the complexity was handled
//! in earlier passes (notably register allocation).

mod sequence_parallel_copies;

use itertools::{Either, Itertools};
use wasmparser::{FuncType, Operator as Op, ValType};

use crate::{
    loader::{
        FunctionAsm, FunctionRef, LabelGenerator, Module, assert_reg,
        passes::{
            blockless_dag::{BreakTarget, Operation, TargetType},
            dag::{NodeInput, ValueOrigin},
        },
        rwm::{
            flattening::sequence_parallel_copies::Register,
            liveness_dag::RangeEndReason,
            register_allocation::{self, AllocatedDag, Allocation, PerNodeOccupation},
            settings::Settings,
        },
        settings::{
            ComparisonFunction, JumpCondition, LabelType, TrapReason, WasmOpInput, format_label,
        },
        split_func_ref_regs, word_count_type, word_count_types,
    },
    utils::{range_consolidation::RangeConsolidationIterator, tree::Tree},
};
use std::{
    collections::{BTreeSet, HashMap, VecDeque},
    ops::Range,
    sync::atomic::AtomicU32,
};

pub fn flatten_dag<'a, S: Settings<'a>>(
    s: &S,
    prog: &Module<'a>,
    label_gen: &AtomicU32,
    func_idx: u32,
    dag: AllocatedDag<'a>,
) -> FunctionAsm<S::Directive> {
    let common_ctx = CommonContext {
        prog,
        label_gen,
        function_name: prog.get_function_name(func_idx),
    };

    let mut ctrl_stack = VecDeque::new();
    ctrl_stack.push_front(StackEntry {
        loop_label: None,
        allocation: dag.block_data,
    });

    let mut flattener = Flattener {
        s,
        common_ctx: &common_ctx,
        ctrl_stack,
        // For each local label, what registers are live at jumps targeting it.
        // This is used to calculate what drops to emit after the label.
        live_regs_at_jump: HashMap::new(),
        func_idx,
    };

    let directives = flattener.process_dag(dag.nodes);

    FunctionAsm {
        func_idx,
        frame_size: None,
        directives: directives.flatten(),
    }
}

struct StackEntry {
    loop_label: Option<String>,
    allocation: Allocation,
}

/// Long-lived state for flattening a single function: settings, function-level
/// context, the nested block stack, the per-label live-register map, and the
/// function index. `process_dag` / `process_node` / `emit_jump` are methods on
/// this so each call site doesn't have to thread these through explicitly.
struct Flattener<'a, 'b, S: Settings<'a>> {
    s: &'b S,
    common_ctx: &'b CommonContext<'a, 'b>,
    ctrl_stack: VecDeque<StackEntry>,
    live_regs_at_jump: HashMap<String, BTreeSet<u32>>,
    func_idx: u32,
}

impl<'a, 'b, S: Settings<'a>> Flattener<'a, 'b, S> {
    fn process_dag(&mut self, nodes: Vec<register_allocation::Node<'a>>) -> Tree<S::Directive> {
        let mut tracker = self.ctrl_stack[0].allocation.per_node_occupation();
        nodes
            .into_iter()
            .enumerate()
            .map(|(node_idx, node)| self.process_node(&mut tracker, node, node_idx))
            .collect_vec()
            .into()
    }

    fn process_node(
        &mut self,
        tracker: &mut PerNodeOccupation,
        node: register_allocation::Node<'a>,
        node_idx: usize,
    ) -> Tree<S::Directive> {
        let mut reg_changes = tracker.advance();
        assert_eq!(reg_changes.node_index, node_idx);

        // Split the set of registers that are consumed from the set that is discarded.
        let (mut consumed_regs, mut discarded_regs): (BTreeSet<_>, BTreeSet<_>) = reg_changes
            .dying
            .into_iter()
            .partition_map(|(reg, reason)| match reason {
                RangeEndReason::Consumed => Either::Left(reg),
                RangeEndReason::Discarded => Either::Right(reg),
            });

        // Destructure the node so we can use parts in separate scopes.
        let register_allocation::Node {
            operation,
            inputs: raw_inputs,
            output_types,
        } = node;

        let allocation = &self.ctrl_stack[0].allocation;

        // Resolve all the inputs to register ranges.
        let inputs = raw_inputs
            .into_iter()
            .map(|input| match input {
                NodeInput::Constant(c) => WasmOpInput::Constant(c),
                NodeInput::Reference(origin) => {
                    WasmOpInput::Register(allocation.get(&origin).unwrap())
                }
            })
            .collect_vec();

        let mut ctx = Context::new(self.common_ctx, allocation, node_idx, &inputs);
        let node_directives = match operation {
            Operation::Inputs => {
                // Inputs node marks the start of the block. If this the toplevel function, we must issue the function label here.
                // Add the function label with the frame size.
                if self.ctrl_stack.len() == 1 {
                    let mut directives = Vec::with_capacity(2);
                    directives.push(
                        self.s
                            .emit_label(&mut ctx, format_label(self.func_idx, LabelType::Function))
                            .into(),
                    );

                    if let Some(name) = ctx.common.prog.get_exported_func(self.func_idx) {
                        // Add an alternative label, using the exported function name.
                        directives.push(self.s.emit_label(&mut ctx, name.to_string()).into());
                    }
                    directives.into()
                } else {
                    Tree::Empty
                }
            }
            Operation::Label { id } => {
                // The execution always reaches a local label through a jump. Registers dying in
                // the previous PC are not relevant here, as this is unreachable through that path.
                consumed_regs.clear();
                discarded_regs.clear();

                let label = format_label(id, LabelType::Local);
                let entry = &self.ctrl_stack[0];
                let live_at_jump = self.live_regs_at_jump.remove(&label);

                let label = self.s.emit_label(&mut ctx, label).into();

                // If there were registers dying at the jumps targeting this label, we need to emit the drops for them right after the label.
                if let Some(live_at_jump) = live_at_jump {
                    let live_regs_at_label = entry.allocation.occupation_for_node(node_idx);
                    vec![
                        label,
                        emit_drops_after_label(self.s, &mut ctx, live_at_jump, live_regs_at_label)
                            .into(),
                    ]
                    .into()
                } else {
                    label
                }
            }
            Operation::Loop { sub_dag, .. } => {
                let AllocatedDag {
                    nodes: loop_nodes,
                    block_data: loop_allocation,
                } = sub_dag;

                // Find where the loop expects its inputs to be.
                let input_ranges = loop_allocation.get_for_node(0);

                // Copy the loop inputs if needed.
                assert!(reg_changes.newly_live.is_empty());
                let mut loop_directives = copy_inputs_if_needed(
                    self.s,
                    &mut ctx,
                    &inputs,
                    input_ranges,
                    &mut consumed_regs,
                );

                // All the node inputs are part of the copy, so all consumed registers
                // should have been handled by the copy.
                assert!(consumed_regs.is_empty());

                // Generate loop label.
                let loop_label = ctx.new_label(LabelType::Loop);
                loop_directives.push(self.s.emit_label(&mut ctx, loop_label.clone()).into());

                // We need to disassemble the context to reassemble later,
                // because we need to mutate self.ctrl_stack.
                let Context {
                    function_call_prelude_size,
                    tmp_tracker,
                    ..
                } = ctx;

                // Process the loop body.
                self.ctrl_stack.push_front(StackEntry {
                    loop_label: Some(loop_label),
                    allocation: loop_allocation,
                });
                let loop_tree = self.process_dag(loop_nodes);
                let sub_entry = self.ctrl_stack.pop_front().unwrap();

                // Get the registers that were live at the call site of the loop.
                let live_at_jump = self
                    .live_regs_at_jump
                    .remove(&sub_entry.loop_label.unwrap())
                    .unwrap_or_default();

                // Generate the drops right after loop label
                let live_regs_at_loop_start = sub_entry.allocation.occupation_for_node(0);
                let mut ctx = Context {
                    common: self.common_ctx,
                    node_index: node_idx,
                    node_inputs: &inputs,
                    function_call_prelude_size,
                    tmp_tracker,
                    allocation: &self.ctrl_stack[0].allocation,
                };

                loop_directives.push(
                    emit_drops_after_label(self.s, &mut ctx, live_at_jump, live_regs_at_loop_start)
                        .into(),
                );

                // Push the loop directives.
                loop_directives.push(loop_tree);
                loop_directives.into()
            }
            Operation::Br(break_target) => {
                assert!(reg_changes.newly_live.is_empty());

                let jump_directives = self
                    .emit_jump(&mut ctx, break_target, &inputs, &mut consumed_regs)
                    .into_tree(self.s);

                // All consumed_reg must have been used by the branch,
                // because the instruction itself takes no operands (unlike BrIf[Zero] and BrTable).
                assert!(consumed_regs.is_empty());

                jump_directives
            }
            Operation::BrIf(target) | Operation::BrIfZero(target) => {
                let (cond, inverse_cond) = match operation {
                    Operation::BrIf(..) => (JumpCondition::IfNotZero, JumpCondition::IfZero),
                    Operation::BrIfZero(..) => (JumpCondition::IfZero, JumpCondition::IfNotZero),
                    _ => unreachable!(),
                };

                // Get the conditional variable from the inputs.
                let (cond_reg, inputs) = ctx.node_inputs.split_last().unwrap();
                let cond_reg = cond_reg.as_register().unwrap().clone();
                assert_reg::<S>(&cond_reg, ValType::I32);

                assert!(reg_changes.newly_live.is_empty());

                // Must clone consumed_regs, because the we also need to emit the drops if branch
                // is not taken, done in the outer scope.
                let mut branch_taken_consumed = consumed_regs.clone();
                let mut jump_directives =
                    self.emit_jump(&mut ctx, target, inputs, &mut branch_taken_consumed);

                // If the selector is being consumed and not needed if branch taken, it
                // will be left on the set of consumed registers. In this case, it must be
                // dropped unconditionally, and is handled as a special case.
                let drop_selector = if branch_taken_consumed.remove(&cond_reg.start) {
                    consumed_regs.remove(&cond_reg.start);
                    true
                } else {
                    false
                };

                // After removing the selector, there shouldn't be any consumed register left.
                assert!(branch_taken_consumed.is_empty());

                // We must save all the currently live registers so that the target label can emit the relevant drops.
                let live_regs = ctx.allocation.occupation_for_node(node_idx);
                self.save_live_at_jump(
                    &mut ctx,
                    &mut jump_directives,
                    &live_regs,
                    BTreeSet::new(), // branch_taken_consumed is empty
                );

                let mut directives = Vec::new();
                if drop_selector {
                    directives.push(
                        self.s
                            .emit_drop_on_next_instr(&mut ctx, cond_reg.start)
                            .into(),
                    );
                }

                if S::is_jump_condition_available(cond)
                    && let JumpResult::PlainJump(target) = jump_directives
                {
                    directives.push(
                        self.s
                            .emit_conditional_jump(&mut ctx, cond, target, cond_reg)
                            .into(),
                    );
                } else {
                    let jump_directives = jump_directives.into_tree(self.s);
                    if S::is_jump_condition_available(inverse_cond) {
                        // Uses branch on inverse condition for the general case. This is the second best case.
                        let cont_label = ctx.new_label(LabelType::Local);
                        directives.extend([
                            // Emit the jump to continuation if the condition is non-zero.
                            self.s
                                .emit_conditional_jump(
                                    &mut ctx,
                                    inverse_cond,
                                    cont_label.clone(),
                                    cond_reg,
                                )
                                .into(),
                            // Emit the jump to the target label.
                            jump_directives,
                            // Emit the continuation label.
                            self.s.emit_label(&mut ctx, cont_label).into(),
                        ]);
                    } else if S::is_jump_condition_available(cond) {
                        // Uses conditional branch for the general case. This is the worst case, because it
                        // it requires two labels and two jumps.
                        let cont_label = ctx.new_label(LabelType::Local);
                        let jump_label = ctx.new_label(LabelType::Local);

                        directives.extend([
                            // Emit the jump to the to the jump code
                            self.s
                                .emit_conditional_jump(&mut ctx, cond, jump_label.clone(), cond_reg)
                                .into(),
                            // Emit the jump to the continuation label.
                            self.s.emit_jump(cont_label.clone()).into(),
                            // Emit the jump label.
                            self.s.emit_label(&mut ctx, jump_label).into(),
                            // Emit the jump code.
                            jump_directives,
                            // Emit the continuation label.
                            self.s.emit_label(&mut ctx, cont_label).into(),
                        ]);
                    } else {
                        panic!(
                            "Neither branch if zero nor branch if not zero is available in the settings."
                        );
                    }
                }

                directives.into()
            }
            Operation::BrTable { targets } => {
                assert!(reg_changes.newly_live.is_empty());

                let (selector, table_inputs) = inputs.split_last().unwrap();
                let selector = selector.as_register().unwrap().clone();

                let live_regs = ctx.allocation.occupation_for_node(node_idx);

                let mut choice_inputs = Vec::with_capacity(table_inputs.len());
                let mut jump_instructions = targets
                    .into_iter()
                    .map(|target| {
                        // The inputs for one particular target are a permutation of the inputs
                        // of the BrTable operation.
                        choice_inputs.clear();
                        for &idx in &target.input_permutation {
                            choice_inputs.push(table_inputs[idx as usize].clone());
                        }

                        // Emit the jump to the target label.
                        let mut consumed = consumed_regs.clone();
                        let jump_result =
                            self.emit_jump(&mut ctx, target.target, &choice_inputs, &mut consumed);

                        (jump_result, consumed)
                    })
                    .collect_vec();

                // The last target is special, because it is the default target.
                let (mut default_target, consumed) = jump_instructions.pop().unwrap();
                self.save_live_at_jump(&mut ctx, &mut default_target, &live_regs, consumed);

                // Get the set of registers that were consumed by the node, but not by any of
                // the remaining branch targets. I.e. can be the BrTable selector itself, or
                // inputs consumed by the default branch but not by any of the other branches.
                let mut consumed_intersection =
                    full_intersection(jump_instructions.iter().map(|(_, consumed)| consumed));

                // Decide whether or not to drop the selector at the relative jump instruction.
                let drop_selector = consumed_intersection.remove(&selector.start);

                // We need to save the live registers at each jump, so that the target labels can emit the relevant drops.
                let jump_instructions = jump_instructions
                    .into_iter()
                    .map(|(mut jump_result, mut consumed)| {
                        if drop_selector {
                            // For the non-default targets, the selector will be dropped at the
                            // jump site, so it doesn't need to be dropped at the target.
                            consumed.remove(&selector.start);
                        }

                        self.save_live_at_jump(&mut ctx, &mut jump_result, &live_regs, consumed);
                        jump_result
                    })
                    .collect_vec();

                // We need to handle the default target separately first, because it will be
                // the target in case the selector is out of bounds.
                let mut directives = Vec::new();
                match default_target {
                    JumpResult::PlainJump(target) => {
                        // If the default target is a plain jump to a local label,
                        // just jump if the selector is out of bounds.
                        directives.push(
                            self.s
                                .emit_conditional_jump_cmp_immediate(
                                    &mut ctx,
                                    ComparisonFunction::GreaterThanOrEqualUnsigned,
                                    selector.clone(),
                                    jump_instructions.len() as u32,
                                    target,
                                    false,
                                )
                                .into(),
                        );
                    }
                    JumpResult::CopyJump(_, jump_directives)
                    | JumpResult::Return(jump_directives) => {
                        // If the default target is a complex jump.
                        let table_label = ctx.new_label(LabelType::Local);
                        directives.extend([
                            // Jump to the table if the selector is in bounds.
                            self.s
                                .emit_conditional_jump_cmp_immediate(
                                    &mut ctx,
                                    ComparisonFunction::LessThanUnsigned,
                                    selector.clone(),
                                    jump_instructions.len() as u32,
                                    table_label.clone(),
                                    false,
                                )
                                .into(),
                        ]);

                        directives.extend([
                            // Otherwise fall through to the default target.
                            jump_directives.into(),
                            // Emit the label for the jump table that will follow.
                            self.s.emit_label(&mut ctx, table_label).into(),
                        ])
                    }
                }

                // Now we drop all consumed inputs that are no longer needed for the remaining targets.
                for reg in consumed_intersection {
                    directives.push(self.s.emit_drop(&mut ctx, reg).into());
                }

                if !S::is_relative_jump_available() {
                    // TODO: emit a sequence of conditional jumps if relative jumps are not available.
                    todo!();
                } else {
                    // TODO: do the way it is currently done below.
                }

                // For robustness, the jump table has two indirections:
                // - jump_offset $selector
                // - choice_0:
                // - jump jump_to_target_0
                // - choice_1:
                // - jump jump_to_target_1
                // - ...
                // - choice_n:
                // - jump jump_to_target_n
                // - jump_to_target_0:
                // - <actual instructions to jump to target 0>
                // - jump_to_target_1:
                // - <actual instructions to jump to target 1>
                // - ...
                // - jump_to_target_n:
                // - <actual instructions to jump to target n>
                //
                // The exception is if the target jump contains one single local jump instruction,
                // which can be embedded in the jump table directly.
                //
                // TODO: theoretically, any single instruction can be embedded in the jump table,
                // but it would require the guarantee that further translations wouldn't implement
                // any of them as multiple ISA instructions. It is safer to assume just Jump will
                // remain a single instruction. Maybe also Return?
                //
                // TODO: if jump_offset can jump $selector * N, where N is some immediate, this
                // can be implemented with a single indirection, but that would also require
                // 1-to-1 mapping in all the instructions belonging to the jump table.
                if drop_selector {
                    directives.push(
                        self.s
                            .emit_drop_on_next_instr(&mut ctx, selector.start)
                            .into(),
                    );
                }
                directives.push(self.s.emit_relative_jump(&mut ctx, selector).into());

                let jump_instructions = jump_instructions
                    .into_iter()
                    .filter_map(|jump_directives| {
                        // This label is not actually refereced statically, but it marks
                        // one possible target of the relative jump. It is useful on backends
                        // that rely on labels to find all the possible jump targets.
                        let marker_label = ctx.new_label(LabelType::Marker);
                        directives.push(self.s.emit_label(&mut ctx, marker_label).into());
                        match jump_directives {
                            JumpResult::PlainJump(target) => {
                                // This is a plain jump, just emit it directly.
                                directives.push(self.s.emit_jump(target).into());
                                None
                            }
                            JumpResult::CopyJump(_, jump_directives)
                            | JumpResult::Return(jump_directives) => {
                                // This is a complex jump, we need to create a new label
                                // and do one indirection.
                                let jump_label = ctx.new_label(LabelType::Local);
                                directives.push(self.s.emit_jump(jump_label.clone()).into());
                                Some((jump_label, jump_directives))
                            }
                        }
                    })
                    // Collecting here is essential, because of side effects of pushing
                    // into `directives`.
                    .collect_vec();

                // Finally emit the jump directives for each target.
                for (jump_label, jump_directives) in jump_instructions {
                    directives.push(self.s.emit_label(&mut ctx, jump_label).into());
                    directives.push(jump_directives.into());
                }
                directives.into()
            }
            Operation::WASMOp(Op::Call { function_index }) => {
                let curr_entry = self.ctrl_stack.front().unwrap();

                if let Some((module, function)) = ctx.common.prog.get_imported_func(function_index)
                {
                    // Imported functions are kinda like system calls, and we assume
                    // the implementation can access the input and output registers directly,
                    // so we just have to emit the call directive.
                    let outputs = (0..output_types.len())
                        .map(|output_idx| {
                            curr_entry
                                .allocation
                                .get(&ValueOrigin {
                                    node: node_idx,
                                    output_idx: output_idx as u32,
                                })
                                .unwrap()
                        })
                        .collect_vec();

                    self.s
                        .emit_imported_call(&mut ctx, module, function, &inputs, outputs)
                        .into()
                } else {
                    // Normal function calls requires inputs to be copied to where they are needed in the
                    // function frame, and also may require outputs to be copied to where the users expect
                    // the values.
                    let func_type = &ctx.common.prog.get_func_type(function_index).ty;
                    let call = prepare_function_call(
                        self.s,
                        &mut ctx,
                        &curr_entry.allocation,
                        node_idx,
                        &inputs,
                        func_type,
                        std::mem::take(&mut reg_changes.newly_live),
                        &mut consumed_regs,
                    );

                    // All the inputs goes directly to the called function,
                    // so there shouldn't be any consumed register left.
                    assert!(consumed_regs.is_empty());

                    vec![
                        call.prefix_directives.into(),
                        self.s
                            .emit_function_call(
                                &mut ctx,
                                format_label(function_index, LabelType::Function),
                                call.frame_start,
                                call.ret_pc,
                                call.ret_fp,
                            )
                            .into(),
                        call.suffix_directives.into(),
                    ]
                    .into()
                }
            }
            Operation::WASMOp(Op::CallIndirect {
                table_index,
                type_index,
            }) => {
                let curr_entry = self.ctrl_stack.front().unwrap();

                // The last input of the CallIndirect operation is the table entry, the others are the function arguments.
                let (entry_idx, inputs) = inputs.split_last().unwrap();
                let entry_idx = entry_idx.as_register().unwrap().clone();

                let fn_type = ctx.common.prog.get_type(type_index);
                let call = prepare_function_call(
                    self.s,
                    &mut ctx,
                    &curr_entry.allocation,
                    node_idx,
                    inputs,
                    &fn_type.ty,
                    reg_changes.newly_live,
                    &mut consumed_regs,
                );

                let fn_entry_is_dying = consumed_regs.remove(&entry_idx.start);

                // There shouldn't remain any register in the consumed set by this point.
                assert!(consumed_regs.is_empty());

                // We need to load the function reference from the table, so we allocate
                // the space for it and emit the table.get directive.
                let func_ref_reg = ctx.allocate_tmp_type::<S>(ValType::FUNCREF);

                // Split the components of the function reference:
                let split_ref = split_func_ref_regs::<S>(func_ref_reg.clone());

                // Indirect calls require checking the function type first.
                // We need a label for the OK case.
                let ok_label = ctx.new_label(LabelType::Local);

                // The sequence to load the function reference, check the type,
                // and then perform the indirect call.
                let mut directives = Vec::with_capacity(11);
                directives.push(
                    self.s
                        .emit_wasm_op(
                            &mut ctx,
                            Op::TableGet { table: table_index },
                            &[WasmOpInput::Register(entry_idx.clone())],
                            Some(func_ref_reg),
                        )
                        .into(),
                );

                if fn_entry_is_dying {
                    directives.push(self.s.emit_drop(&mut ctx, entry_idx.start).into());
                }

                directives.extend([
                    // Func frame size is not used in RW mode.
                    self.s
                        .emit_drop(&mut ctx, split_ref[FunctionRef::<S>::FUNC_FRAME_SIZE].start)
                        .into(),
                    self.s
                        .emit_conditional_jump_cmp_immediate(
                            &mut ctx,
                            ComparisonFunction::Equal,
                            split_ref[FunctionRef::<S>::TYPE_ID].clone(),
                            fn_type.unique_id,
                            ok_label.clone(),
                            // TYPE_ID is no longer needed after this jump.
                            true,
                        )
                        .into(),
                    self.s
                        .emit_drop(&mut ctx, split_ref[FunctionRef::<S>::FUNC_ADDR].start)
                        .into(),
                    self.s
                        .emit_trap(&mut ctx, TrapReason::WrongIndirectCallFunctionType)
                        .into(),
                    self.s.emit_label(&mut ctx, ok_label).into(),
                    call.prefix_directives.into(),
                    self.s
                        .emit_drop_on_next_instr(
                            &mut ctx,
                            split_ref[FunctionRef::<S>::FUNC_ADDR].start,
                        )
                        .into(),
                    self.s
                        .emit_indirect_call(
                            &mut ctx,
                            split_ref[FunctionRef::<S>::FUNC_ADDR].clone(),
                            call.frame_start,
                            call.ret_pc,
                            call.ret_fp,
                        )
                        .into(),
                    call.suffix_directives.into(),
                ]);

                return directives.into();
            }
            Operation::WASMOp(Op::Unreachable) => {
                return self
                    .s
                    .emit_trap(&mut ctx, TrapReason::UnreachableInstruction)
                    .into();
            }
            Operation::WASMOp(op) => {
                // Normal WASM operations are handled by the ISA emmiter directly.
                let curr_entry = self.ctrl_stack.front().unwrap();
                let output = match output_types.len() {
                    0 => None,
                    1 => Some(
                        curr_entry
                            .allocation
                            .get(&ValueOrigin {
                                node: node_idx,
                                output_idx: 0,
                            })
                            .unwrap(),
                    ),
                    _ => {
                        panic!("WASM instructions with multiple outputs! This is a bug.");
                    }
                };
                self.s.emit_wasm_op(&mut ctx, op, &inputs, output).into()
            }
        };

        // The drops must not clobber newly live registers, so we must remove them from
        // the consumed set (i.e., registers were used but overwritten immediately).
        for reg in reg_changes.newly_live {
            consumed_regs.remove(&reg);
        }

        // The general case for the drops:
        // discarded registers are dropped before the node directives,
        // and consumed registers are dropped after.
        if discarded_regs.is_empty() && consumed_regs.is_empty() {
            node_directives
        } else {
            let mut directives = Vec::with_capacity(discarded_regs.len() + consumed_regs.len() + 1);
            for reg in discarded_regs {
                directives.push(self.s.emit_drop(&mut ctx, reg).into());
            }
            directives.push(node_directives);
            for reg in consumed_regs {
                directives.push(self.s.emit_drop(&mut ctx, reg).into());
            }
            directives.into()
        }
    }

    fn save_live_at_jump(
        &mut self,
        ctx: &mut Context<'a, '_>,
        jump_result: &mut JumpResult<S::Directive>,
        currently_live: &[Range<u32>],
        mut consumed_regs: BTreeSet<u32>,
    ) {
        if currently_live.is_empty() && consumed_regs.is_empty() {
            return;
        }

        // We do one last attempt to perform the drops of the remaining
        // consumed registers before the actual jump, if possible.
        if let Some(branched_directives) = jump_result.mut_directives() {
            for reg in std::mem::take(&mut consumed_regs) {
                branched_directives.push(self.s.emit_drop(ctx, reg).into());
            }
        }

        if let Some(target) = jump_result.target() {
            // Whenever this jump is a conditional jump (br_table jumps included), we can have extra "sudden"
            // register deaths: registers that must be kept alive if this branch is not taken, but are no longer
            // needed if this branch is taken. We must save what are the registers that are currently live at the
            // jump, so that the target can know what drops to emit.
            let live_set = self.live_regs_at_jump.entry(target.clone()).or_default();
            for range in currently_live {
                for reg in range.clone() {
                    live_set.insert(reg);
                }
            }

            // Whatever remains in consumed_regs must also be dropped at the target label.
            for reg in consumed_regs {
                live_set.insert(reg);
            }
        }
    }

    fn emit_jump(
        &self,
        ctx: &mut Context<'a, '_>,
        target: BreakTarget,
        inputs: &[WasmOpInput],
        consumed_regs: &mut BTreeSet<u32>,
    ) -> JumpResult<S::Directive> {
        // There are 3 different kinds of jumps we have to deal with:
        //
        // 1. Jumps to a forward label in the current function.
        // 2. Jump backwards to a loop iteration.
        // 3. Returns from the function.

        let target_entry = &self.ctrl_stack[target.depth as usize];
        let allocation = &target_entry.allocation;
        let (output_node_idx, target) = match target.kind {
            TargetType::Loop => {
                let loop_label = target_entry
                    .loop_label
                    .as_ref()
                    .expect("Loop target should have a loop label");

                // This is a jump to a new loop iteration.
                // The node whose outputs we want are the Inputs node of the loop (index 0).
                (0, loop_label.as_str().into())
            }
            TargetType::Function => {
                assert!(target_entry.loop_label.is_none());
                // This is a return from the function.
                // Calculate the outputs registers from the function type.
                let func_type = &ctx.common.prog.get_func_type(self.func_idx).ty;
                let ret_types = func_type.results();
                // They are tightly packed at the top of the frame.
                let mut fn_output_size = 0;
                let input_ranges = ranges_for_types::<S>(ret_types, &mut fn_output_size);

                // Use the current block's allocation to source the copied inputs:
                let mut directives =
                    copy_inputs_if_needed(self.s, ctx, inputs, input_ranges, consumed_regs);

                // Also calculate the space needed by the function inputs, to calculate where
                // the return address and caller frame pointer are stored.
                let fn_input_size = word_count_types::<S>(func_type.params());
                let (ra, caller_fp) = calculate_ra_and_fp::<S>(fn_input_size, fn_output_size);

                directives.push(self.s.emit_return(ctx, ra, caller_fp).into());

                return JumpResult::Return(directives);
            }
            TargetType::Label(id) => {
                // This is a jump to a label in the current function.
                // The node we want is the target label's node.
                (
                    target_entry.allocation.labels[&id],
                    format_label(id, LabelType::Local),
                )
            }
        };

        let input_ranges = allocation.get_for_node(output_node_idx);
        let mut directives =
            copy_inputs_if_needed(self.s, ctx, inputs, input_ranges, consumed_regs);
        if directives.is_empty() {
            JumpResult::PlainJump(target)
        } else {
            directives.push(self.s.emit_jump(target.clone()).into());
            JumpResult::CopyJump(target, directives)
        }
    }
}

enum JumpResult<D> {
    Return(Vec<Tree<D>>),
    CopyJump(String, Vec<Tree<D>>),
    PlainJump(String),
}

impl<D> JumpResult<D> {
    fn into_tree<'a, S: Settings<'a>>(self, s: &S) -> Tree<D>
    where
        Tree<D>: From<S::Directive>,
    {
        match self {
            JumpResult::CopyJump(_, directives) | JumpResult::Return(directives) => {
                directives.into()
            }
            JumpResult::PlainJump(target) => s.emit_jump(target).into(),
        }
    }

    fn mut_directives(&mut self) -> Option<&mut Vec<Tree<D>>> {
        match self {
            JumpResult::CopyJump(_, directives) | JumpResult::Return(directives) => {
                Some(directives)
            }
            JumpResult::PlainJump(_) => None,
        }
    }

    fn target(&self) -> Option<&String> {
        match self {
            JumpResult::CopyJump(target, _) | JumpResult::PlainJump(target) => Some(target),
            JumpResult::Return(_) => None,
        }
    }
}

fn emit_drops_after_label<'a, S: Settings<'a>>(
    s: &S,
    ctx: &mut Context<'a, '_>,
    live_at_jump: BTreeSet<u32>,
    live_regs_at_label: Vec<Range<u32>>,
) -> Vec<Tree<S::Directive>> {
    let mut to_drop = live_at_jump;
    for range in live_regs_at_label {
        for reg in range {
            to_drop.remove(&reg);
        }
    }

    to_drop
        .into_iter()
        .map(|reg| s.emit_drop(ctx, reg).into())
        .collect_vec()
}

/// Every control flow that has inputs needs them at specific locations.
///
/// This function emits the copy instructions for the inputs that are not
/// already at the expected locations, and the drops for the inputs are
/// no longer used after the copy. It also cleans the consumed_regs of registers
/// that can't be dropped because they are expected in that place as input.
///
/// Registers that are not related to the copy are left in `consumed_regs`.
fn copy_inputs_if_needed<'a, S: Settings<'a>>(
    s: &S,
    ctx: &mut Context<'a, '_>,
    node_inputs: &[WasmOpInput],
    expected_locations: impl IntoIterator<Item = Range<u32>>,
    consumed_regs: &mut BTreeSet<u32>,
) -> Vec<Tree<S::Directive>> {
    let copy_set = node_inputs
        .iter()
        .zip_eq(expected_locations)
        .filter_map(|(input, destiny)| {
            // Any register that is in the destiny range can't be dropped after
            // the copy is complete.
            for reg in destiny.clone() {
                consumed_regs.remove(&reg);
            }

            let source = input.as_register().unwrap().clone();
            (source != destiny).then_some((source, destiny))
        })
        .collect_vec();

    // TODO: If there are no copies to be done, drops are not immeditelly emmited.
    // compare with the case where we emit the drops immediately, as it might
    // worsen naive execution (as it requires one extra jump indirection)
    // but might improve APC.
    if copy_set.is_empty() {
        return Vec::new();
    }

    // drops is defined as (dying_regs ∩ source regs) - destination regs.
    // I.e. everything that is read that isn't colocated with the output set.
    let mut drops = BTreeSet::new();
    for (source, _) in &copy_set {
        for reg in source.clone() {
            // Set a dying register to be dropped.
            if consumed_regs.remove(&reg) {
                drops.insert(reg);
            }
        }
    }

    let (tmp_register, mut directives) = parallel_copy(s, ctx, copy_set);
    if let Some(tmp_register) = tmp_register {
        // If a temporary register was needed, we need to drop it, too.
        drops.insert(tmp_register);
    }

    // Emit the drops for the registers that are dying after the copy.
    for reg in drops {
        directives.push(s.emit_drop(ctx, reg).into());
    }

    directives
}

/// Given a set of source-destination register ranges, emits the sequence of copy instructions
/// such that all copies are performed correctly, even in presence of overlapping ranges.
fn parallel_copy<'a, S: Settings<'a>>(
    s: &S,
    ctx: &mut Context<'a, '_>,
    copy_set: Vec<(Range<u32>, Range<u32>)>,
) -> (Option<u32>, Vec<Tree<S::Directive>>) {
    // Turn a set of range copies into a set of single register copies.
    let copy_set = copy_set
        .into_iter()
        .flat_map(|(source_range, dest_range)| source_range.into_iter().zip(dest_range));
    let copy_sequence = sequence_parallel_copies::sequence_parallel_copies(copy_set);

    // Just allocate a temporary register if needed.
    let mut tmp_register = None;
    let mut materialize = |ctx: &mut Context<'a, '_>, reg| -> u32 {
        match reg {
            Register::Temp => match tmp_register {
                Some(tmp_reg) => tmp_reg,
                None => {
                    let new_tmp = ctx.allocate_tmp_type::<S>(ValType::I32);
                    assert_eq!(new_tmp.len(), 1);
                    let new_tmp = new_tmp.start;
                    tmp_register = Some(new_tmp);
                    new_tmp
                }
            },
            Register::Given(reg) => reg,
        }
    };

    let directives = copy_sequence
        .map(|(src, dest)| {
            let src = materialize(ctx, src);
            let dest = materialize(ctx, dest);
            s.emit_copy(ctx, src, dest).into()
        })
        .collect_vec();
    (tmp_register, directives)
}

/// Calculates the register address for a tightly packed list types.
fn ranges_for_types<'a, S: Settings<'a>>(
    types: &[ValType],
    start_offset: &mut u32,
) -> impl Iterator<Item = Range<u32>> {
    types.iter().scan(start_offset, |offset, ty| {
        let size = word_count_type::<S>(*ty);
        let start = **offset;
        **offset += size;
        Some(start..**offset)
    })
}

fn calculate_ra_and_fp<'a, S: Settings<'a>>(
    input_size: u32,
    output_size: u32,
) -> (Range<u32>, Range<u32>) {
    let ra_ptr = input_size.max(output_size);
    let caller_fp_ptr = ra_ptr + S::words_per_ptr();

    let ra = ra_ptr..caller_fp_ptr;
    let caller_fp = caller_fp_ptr..(caller_fp_ptr + S::words_per_ptr());
    (ra, caller_fp)
}

/// Context for the flattening process of the entire function.
struct CommonContext<'a, 'b> {
    prog: &'b Module<'a>,
    label_gen: &'b AtomicU32,
    function_name: Option<&'a str>,
}

/// A context built per node being processed, that tracks the
/// temporary registers needed when translating just that node.
pub struct Context<'a, 'b> {
    common: &'b CommonContext<'a, 'b>,
    allocation: &'b Allocation,
    node_index: usize,
    node_inputs: &'b [WasmOpInput],
    /// This is needed for the tmp_tracker to work when a tmp is
    /// requested during the translation of a function call.
    /// In that case, most of the register space will be occupied by
    /// the function call frame, but it is fine to allocate tmps in that space,
    /// after the space reserved for the calling convention (inputs,
    /// outputs, return address and caller frame pointer).
    function_call_prelude_size: Option<u32>,
    /// If no temporary registers were allocated yet, this is None.
    /// If some were allocated, this tracks all the holes in the
    /// frame that can be used for further temporary allocations,
    /// kept in reverse sorted order.
    tmp_tracker: Option<Vec<Range<u32>>>,
}

impl<'a, 'b> Context<'a, 'b> {
    fn new(
        common: &'b CommonContext<'a, 'b>,
        allocation: &'b Allocation,
        node_index: usize,
        node_inputs: &'b [WasmOpInput],
    ) -> Self {
        Self {
            common,
            allocation,
            node_index,
            node_inputs,
            function_call_prelude_size: None,
            tmp_tracker: None,
        }
    }

    fn allocate_tmp_words(&mut self, size: u32) -> Range<u32> {
        if self.tmp_tracker.is_none() {
            // This is the first time a temporary is being allocated at this node.
            // We need to figure out what slots are available for temporaries.

            // Get all the occupied ranges for this node.
            let mut occupied_ranges = self.allocation.occupation_for_node(self.node_index);

            // We also need to include the inputs for this node, because in our occupation convention,
            // if this is the last usage of an input, it is already considered free in this node.
            occupied_ranges.extend(
                self.node_inputs
                    .iter()
                    .filter_map(|input| input.as_register().cloned()),
            );

            let mut holes = Vec::new();
            let mut last_occupied = 0..0;
            for occupied in RangeConsolidationIterator::new(occupied_ranges) {
                if occupied.start > last_occupied.end {
                    holes.push(last_occupied.end..occupied.start);
                }
                last_occupied = occupied;
            }

            if let Some(prelude_size) = self.function_call_prelude_size {
                let frame_start = self.allocation.call_frames[&self.node_index];
                // The last occupation must contain the function frame
                assert!(last_occupied.start <= frame_start);
                assert_eq!(last_occupied.end, u32::MAX);

                // We can use the part of the function frame that
                // is not reserved for the calling convention.
                last_occupied.end = frame_start + prelude_size;
            }

            if last_occupied.end < u32::MAX {
                holes.push(last_occupied.end..u32::MAX);
            }
            holes.reverse(); // So we can allocate from the end.
            self.tmp_tracker = Some(holes);
        }

        let tmp_tracker = self.tmp_tracker.as_mut().unwrap();

        for idx in (0..tmp_tracker.len()).rev() {
            let hole = &mut tmp_tracker[idx];
            if hole.len() as u32 >= size {
                let alloc_end = hole.start + size;
                let allocated = hole.start..alloc_end;
                if alloc_end == hole.end {
                    // The hole is fully used up.
                    //
                    // I would like to use a LinkedList here, but Rust has no stable API
                    // to remove an element from the middle of a LinkedList in O(1) time,
                    // (cursor API is unstable) so even Vec's O(n) removal is better here.
                    //
                    // The search is done from the end in order to minimize the number of
                    // of elements shifted when removing. If the first hole is used, no
                    // element needs to be shifted.
                    tmp_tracker.remove(idx);
                } else {
                    // Shrink the hole.
                    hole.start = alloc_end;
                }
                return allocated;
            }
        }
        panic!("Full register space exhausted when allocating temporary registers.");
    }

    /// Allocates a temporary register that is only valid for the sequence of instructions
    /// you are emitting.
    pub fn allocate_tmp_type<S: Settings<'a>>(&mut self, ty: ValType) -> Range<u32> {
        self.allocate_tmp_words(word_count_type::<S>(ty))
    }

    pub fn new_label(&self, label_type: LabelType) -> String {
        format_label(self.common.label_gen.next(), label_type)
    }

    pub fn function_name(&self) -> Option<&str> {
        self.common.function_name
    }

    /// Returns a reference to the module being processed.
    ///
    /// The returned reference has lifetime `'b` (independent of the `&self` borrow),
    /// so callers can use it alongside `&mut self` without borrow conflicts.
    pub fn module(&self) -> &'b Module<'a> {
        self.common.prog
    }
}

struct FunctionCall<D> {
    frame_start: u32,
    prefix_directives: Vec<Tree<D>>,
    suffix_directives: Vec<Tree<D>>,
    ret_pc: Range<u32>,
    ret_fp: Range<u32>,
}

fn prepare_function_call<'a, S: Settings<'a>>(
    s: &S,
    ctx: &mut Context<'a, '_>,
    allocation: &Allocation,
    node_idx: usize,
    inputs: &[WasmOpInput],
    func_type: &FuncType,
    mut newly_live: Vec<u32>,
    consumed_regs: &mut BTreeSet<u32>,
) -> FunctionCall<S::Directive> {
    // Normal function calls requires inputs to be copied to where they are needed in the
    // function frame, and also may require outputs to be copied to where the users expect
    // the values.

    let frame_start = allocation.call_frames[&node_idx];

    // Get where the inputs should be copied to.
    let mut inputs_offset = frame_start;
    let input_ranges = ranges_for_types::<S>(func_type.params(), &mut inputs_offset).collect_vec();

    // Get where the outputs should be copied from.
    let mut outputs_offset = frame_start;
    let output_copy_set = ranges_for_types::<S>(func_type.results(), &mut outputs_offset)
        .enumerate()
        .filter_map(|(output_idx, src_range)| {
            let output_origin = ValueOrigin {
                node: node_idx,
                output_idx: output_idx as u32,
            };
            let dest_range = allocation.get(&output_origin).unwrap();
            assert_eq!(src_range.len(), dest_range.len());

            (dest_range != src_range).then_some((src_range, dest_range))
        })
        .collect_vec();

    // Calculate the space needed by the function inputs/outputs, to calculate where
    // the return address and caller frame pointer are stored.
    let input_size = inputs_offset - frame_start;
    let outputs_size = outputs_offset - frame_start;
    let (ret_pc, ret_fp) = calculate_ra_and_fp::<S>(input_size, outputs_size);

    // Set the end of the function call prelude, so tmps can be allocated in the function frame if needed.
    ctx.function_call_prelude_size = Some(ret_fp.end);

    // Generate the actual directives for input and output copy.
    let prefix_directives = copy_inputs_if_needed(s, ctx, inputs, input_ranges, consumed_regs);

    let (tmp_reg, mut suffix_directives) = parallel_copy(s, ctx, output_copy_set);

    // After the function is called, we need another set of drops to clear the function frame.
    let mut individual_drops = Vec::new();
    if let Some(tmp_reg) = tmp_reg
        && tmp_reg < frame_start
    {
        individual_drops.push(tmp_reg);
    }

    // Everything from frame_start onward that is not a newly live value must be dropped.
    // I.e. we must keep used function outputs that were allocated inside the callee frame,
    // and drop the rest of the frame. This should already include every ephemeral output.
    newly_live.retain(|reg| *reg >= frame_start);
    newly_live.sort_unstable();
    let mut drop_from = frame_start;
    for reg in newly_live {
        individual_drops.extend(drop_from..reg);
        drop_from = reg + 1;
    }

    // Emit the after-call drops
    for reg in individual_drops {
        suffix_directives.push(s.emit_drop(ctx, reg).into());
    }
    suffix_directives.push(s.emit_drop_from(ctx, drop_from).into());

    FunctionCall {
        frame_start,
        prefix_directives,
        suffix_directives,
        ret_pc,
        ret_fp,
    }
}

/// Intersection of all sets. Assumes the iterator is non-empty.
fn full_intersection<'a, T, I>(sets: I) -> BTreeSet<T>
where
    T: Ord + Clone + 'a,
    I: IntoIterator<Item = &'a BTreeSet<T>>,
{
    let mut sets: Vec<&BTreeSet<T>> = sets.into_iter().collect();
    sets.sort_unstable_by_key(|s| s.len());

    let (smallest, rest) = sets.split_first().expect("input must be non-empty");

    smallest
        .iter()
        .filter(|x| rest.iter().all(|s| s.contains(*x)))
        .cloned()
        .collect()
}
