//! Removes labels that are never targeted by a jump, along with all
//! nodes from each unused label up to (but not including) the next
//! label or the end of the block.
//!
//! Right after the blockless DAG pass, a label can only be reached via
//! an explicit jump (`Br`, `BrIf`, `BrIfZero`, `BrTable`, or a `Loop`
//! that breaks to it). So a label without any incoming jump is dead,
//! and the linear chunk of nodes following it (up to the next label)
//! is unreachable.
//!
//! Within a block, jumps never go backwards, so all jumps targeting a
//! given label appear before the label in linear node order. That lets
//! us decide in a single forward pass whether a label is used: when we
//! reach it, every potential incoming jump has already been seen.

use std::collections::HashSet;

use crate::loader::passes::blockless_dag::{
    BlocklessDag, GenericBlocklessDag, NodeInput, Operation, TargetType,
};

pub fn remove_unreachable_code(dag: &mut BlocklessDag) -> usize {
    remove_inner(dag)
}

fn remove_inner<T>(dag: &mut GenericBlocklessDag<'_, T>) -> usize {
    let nodes = std::mem::take(&mut dag.nodes);
    let mut new_nodes = Vec::with_capacity(nodes.len());
    let mut idx_map = vec![usize::MAX; nodes.len()];
    let mut used_labels: HashSet<u32> = HashSet::new();
    let mut skipping = false;
    let mut removed = 0;

    for (old_idx, mut node) in nodes.into_iter().enumerate() {
        if let Operation::Loop { sub_dag, .. } = &mut node.operation {
            removed += remove_inner(sub_dag);
        }

        let keep = match &node.operation {
            Operation::Label { id } => {
                let used = used_labels.contains(id);
                skipping = !used;
                used
            }
            _ => !skipping,
        };

        if !keep {
            removed += 1;
            continue;
        }

        for input in node.inputs.iter_mut() {
            if let NodeInput::Reference(origin) = input {
                origin.node = idx_map[origin.node];
            }
        }

        register_targets(&node.operation, &mut used_labels);

        idx_map[old_idx] = new_nodes.len();
        new_nodes.push(node);
    }

    dag.nodes = new_nodes;
    removed
}

fn register_targets<T>(operation: &Operation<'_, T>, used_labels: &mut HashSet<u32>) {
    match operation {
        Operation::Br(target) | Operation::BrIf(target) | Operation::BrIfZero(target) => {
            insert_if_local_label(used_labels, target.depth, target.kind);
        }
        Operation::BrTable { targets } => {
            for t in targets {
                insert_if_local_label(used_labels, t.target.depth, t.target.kind);
            }
        }
        Operation::Loop { break_targets, .. } => {
            if let Some((depth, kinds)) = break_targets.first()
                && *depth == 0
            {
                for kind in kinds {
                    if let TargetType::Label(id) = kind {
                        used_labels.insert(*id);
                    }
                }
            }
        }
        _ => {}
    }
}

fn insert_if_local_label(used_labels: &mut HashSet<u32>, depth: u32, kind: TargetType) {
    if depth == 0
        && let TargetType::Label(id) = kind
    {
        used_labels.insert(id);
    }
}
