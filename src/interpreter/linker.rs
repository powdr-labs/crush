use std::collections::HashMap;

use crate::loader::{FunctionAsm, rwm::settings::DropHint};

pub struct Label<'a> {
    pub id: &'a str,
    pub namespace: Option<&'a str>,
    pub frame_size: Option<u32>,
}

/// A drop hint resolved to its execution position relative to an instruction.
///
/// These live in the side channel produced by the linker, indexed by the PC of
/// the instruction they apply to. Backends that don't track register liveness
/// can ignore the side channel entirely.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecDropHint {
    /// Drop the register before executing the instruction at this PC.
    DropBefore(u32),
    /// Drop all registers from this one onward before executing the instruction at this PC.
    DropBeforeFrom(u32),
    /// Drop the register after executing the instruction at this PC.
    DropAfter(u32),
}

pub trait Directive: Clone {
    fn nop() -> Self;
    fn as_label(&self) -> Option<Label<'_>>;
    /// If this directive is a drop hint, returns it. Drop hints are stripped
    /// from the linked program and moved into the side channel.
    fn as_drop_hint(&self) -> Option<DropHint>;
}

#[derive(Debug)]
pub struct LabelValue {
    pub pc: u32,
    pub frame_size: Option<u32>,
    pub func_idx: Option<u32>,
    pub namespace: Option<String>,
}

pub fn link<D: Directive>(
    program: Vec<FunctionAsm<D>>,
    init_pc: u32,
) -> (Vec<D>, HashMap<String, LabelValue>, Vec<Vec<ExecDropHint>>) {
    let mut flat_program = vec![D::nop(); init_pc as usize];
    // Side channel of drop hints, indexed by PC and kept parallel to `flat_program`.
    let mut drop_hints: Vec<Vec<ExecDropHint>> = vec![Vec::new(); init_pc as usize];
    let mut labels = HashMap::new();

    for fun in program {
        let func_pc = flat_program.len() as u32;

        // Drop hints bind forward to the next real instruction. We buffer them
        // here and flush them onto that instruction's PC when we reach it.
        let mut pending: Vec<ExecDropHint> = Vec::new();
        // Set while a `DropAfter` hint is buffered: no label may sit between it
        // and the instruction it applies to.
        let mut after_hint_open = false;

        for d in fun.directives {
            if let Some(hint) = d.as_drop_hint() {
                match hint {
                    DropHint::DropNow(r) => pending.push(ExecDropHint::DropBefore(r)),
                    DropHint::DropNowFrom(r) => pending.push(ExecDropHint::DropBeforeFrom(r)),
                    DropHint::DropAfterNextInstruction(r) => {
                        pending.push(ExecDropHint::DropAfter(r));
                        after_hint_open = true;
                    }
                }
                continue;
            }

            match d.as_label() {
                Some(Label {
                    id,
                    namespace,
                    frame_size,
                }) => {
                    assert!(
                        !after_hint_open,
                        "label between a DropAfterNextInstruction hint and its instruction"
                    );
                    let pc = flat_program.len() as u32;
                    labels.insert(
                        id.to_string(),
                        LabelValue {
                            pc,
                            frame_size,
                            func_idx: (pc == func_pc).then_some(fun.func_idx),
                            namespace: namespace.map(str::to_string),
                        },
                    );
                }
                None => {
                    flat_program.push(d);
                    drop_hints.push(std::mem::take(&mut pending));
                    after_hint_open = false;
                }
            }
        }

        // Every drop hint must have bound to an instruction within the function.
        assert!(
            pending.is_empty(),
            "dangling drop hints at the end of a function"
        );
    }

    debug_assert_eq!(flat_program.len(), drop_hints.len());
    (flat_program, labels, drop_hints)
}
