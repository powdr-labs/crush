//! This module implements a pass to remove orphaned local labels, i.e.
//! labels that are never jumped to by any instruction.
//!
//! This must be done after dumb_jump_removal, because jumps removed there
//! might leave some labels orphaned.
//!
//! This pass is useful to backends that use labels to detect jump targets
//! for further optimizations, thus removing false positives.

use crate::loader::{
    FunctionAsm,
    settings::{LOCAL_LABEL_PREFIX, Settings},
};
use hashbrown::HashSet;

pub fn remove_orphan_labels<S: Settings>(asm: &mut FunctionAsm<S::Directive>) -> usize {
    // Collect all local labels that are jumped to by some instruction.
    let mut used_labels = HashSet::new();
    for directive in &asm.directives {
        if let Some(target) = S::get_static_target(directive)
            && target.starts_with(LOCAL_LABEL_PREFIX)
        {
            used_labels.get_or_insert_with(&target[LOCAL_LABEL_PREFIX.len()..], str::to_string);
        }
    }

    // Filter out directives that are labels not in the used set.
    let mut removed_count = 0;
    asm.directives.retain(|directive| {
        if let Some(label) = S::is_label(directive)
            && label.starts_with(LOCAL_LABEL_PREFIX)
            && !used_labels.contains(&label[LOCAL_LABEL_PREFIX.len()..])
        {
            removed_count += 1;
            false
        } else {
            true
        }
    });

    removed_count
}
