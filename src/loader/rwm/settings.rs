use std::ops::Range;
use wasmparser::Operator;

use crate::{
    loader::{
        self,
        rwm::flattening::Context,
        settings::{ComparisonFunction, JumpCondition, TrapReason, WasmOpInput},
    },
    utils::tree::Tree,
};

/// A drop hint, signaling that one or more registers are no longer needed at
/// some point. These are pure hints: backends that don't track register
/// liveness can safely ignore them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DropHint {
    /// The given register is no longer needed at this point.
    DropNow(u32),
    /// The given register will no longer be needed after the next instruction.
    DropAfterNextInstruction(u32),
    /// All registers from the given one onward (in the current frame) are no
    /// longer needed.
    DropNowFrom(u32),
}

/// Trait controlling the behavior of the flattening process.
pub trait Settings<'a>: loader::Settings {
    /// Emits a directive to mark a code position.
    ///
    /// Every jump target is market with at least one label.
    fn emit_label(&self, c: &mut Context<'a, '_>, name: String)
    -> impl Into<Tree<Self::Directive>>;

    /// Emits a trap instruction with the given reason.
    fn emit_trap(
        &self,
        c: &mut Context<'a, '_>,
        trap: TrapReason,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Copies a single word between two registers.
    fn emit_copy(
        &self,
        c: &mut Context<'a, '_>,
        src_reg: u32,
        dest_reg: u32,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits conditional jump to a label.
    ///
    /// The condition type will be one of the available, as per
    /// `is_branch_if_zero_available()` and `is_branch_if_not_zero_available()`.
    fn emit_conditional_jump(
        &self,
        c: &mut Context<'a, '_>,
        condition_type: JumpCondition,
        label: String,
        condition_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a jump to a label conditioned on cmp(value, immediate).
    ///
    /// last_reg_usage will be set to true if this is the last usage of the value
    /// in value_ptr, and false otherwise. This can be used to optimize register usage.
    fn emit_conditional_jump_cmp_immediate(
        &self,
        c: &mut Context<'a, '_>,
        cmp: ComparisonFunction,
        value_ptr: Range<u32>,
        immediate: u32,
        label: String,
        last_reg_usage: bool,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a jump relative to the next instruction (i.e. to PC+1+offset, where offset is unsigned).
    ///
    /// If offset is 0, it is equivalent to a NOP. Otherwise, it skips as many instructions as the offset.
    fn emit_relative_jump(
        &self,
        c: &mut Context<'a, '_>,
        offset_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a function return instruction.
    fn emit_return(
        &self,
        c: &mut Context<'a, '_>,
        ret_pc_ptr: Range<u32>,
        caller_fp_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a call to an imported function.
    fn emit_imported_call(
        &self,
        c: &mut Context<'a, '_>,
        module: &'a str,
        function: &'a str,
        inputs: &[WasmOpInput],
        outputs: Vec<Range<u32>>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a call to a local function.
    ///
    /// `saved_ret_pc_ptr` and `saved_caller_fp_ptr` are given in callee's frame space.
    fn emit_function_call(
        &self,
        c: &mut Context<'a, '_>,
        function_label: String,
        function_frame_offset: u32,
        saved_ret_pc_ptr: Range<u32>,
        saved_caller_fp_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a call to a local function via a function pointer.
    ///
    /// `saved_ret_pc_ptr` and `saved_caller_fp_ptr` are given in callee's frame space.
    fn emit_indirect_call(
        &self,
        c: &mut Context<'a, '_>,
        target_pc_ptr: Range<u32>,
        function_frame_offset: u32,
        saved_ret_pc_ptr: Range<u32>,
        saved_caller_fp_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits the equivalent set of instructions to a WASM operation.
    fn emit_wasm_op(
        &self,
        c: &mut Context<'a, '_>,
        op: Operator<'a>,
        inputs: &[WasmOpInput],
        output: Option<Range<u32>>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a drop hint, signaling that one or more registers are no longer needed.
    ///
    /// Drop hints are pure liveness information and carry no semantic meaning:
    /// backends that don't track register liveness can safely ignore them.
    fn emit_drop_hint(
        &self,
        c: &mut Context<'a, '_>,
        hint: DropHint,
    ) -> impl Into<Tree<Self::Directive>>;
}
