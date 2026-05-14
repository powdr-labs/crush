import ParallelCopies.Phase2

/-!
# Algorithm-level proofs — current state

This module re-exports the proofs from `Phase1` and `Phase2` and tracks
progress toward the full `sequenceParallelCopies_correct` theorem.

All committed theorems are axiom-clean (depend only on `propext`,
`Classical.choice`, `Quot.sound` — Lean's three foundational axioms;
no `sorry`, no `nativeDecide`).

## Theorems proved

### Empty-input correctness (full algorithm)

* `sequenceParallelCopies_correct_on_empty` — for `pairs = #[]`, the
  algorithm matches the parallel spec on every register and every
  initial state.

### Spec lemmas (`SpecLemmas.lean`)

14 theorems: `applyParallel_*`, `applySequential_*`, `step_*`, `lift_*`,
`findWriter?_*`, `Pair.appliesTo_*`, `realisesParallel_emptyImpl_on_empty`.

### List-based mirror (`ListSpec.lean`)

9 theorems: `applyParallelL_*`, `applyParallelLS_*`, `applySequentialL_*`,
plus the Array↔List bridges (`applySequential_eq_L`, `applyParallel_eq_L`).

### Phase 1 (tree pruning with source-swap) — `Phase1.lean`

* Leaf / `UniqueDst` / `Pair.appliesTo` structural lemmas.
* `find?_peelStep_self`, `find?_dst_of_mem`, `find?_of_no_writer`.
* `mem_peelStep`, `peelStep_uniqueDst`, `peelStep_no_self`.
* `find?_peelStep_ne` — characterisation of `find?` on `peelStep` for
  non-peeled destinations.
* **`peelStep_sound`** — full source-swap soundness (central Phase 1 lemma).
* **`phase1_sound`** — full Phase 1 induction invariant.

### Phase 2 (cycle breaking) — `Phase2.lean`

* `mem_eraseDst`, `eraseDst_uniqueDst`, `eraseDst_no_self`.
* `srcOf?_mem`, `srcOf?_eraseDst_self`, `srcOf?_eraseDst_ne`.
* `walkCycle_acc_prefix`, `walkCycle_emits_given`.
* `walkCycle_emits_eq` — walkCycle's emits factored from its accumulator.
* `walkEmits_dsts` — walkEmits's destinations characterised structurally.
* **`walkEmits_dsts_nodup`** — destinations of `walkEmits` are pairwise
  distinct.
* **`applySequentialL_at_dst_unique`** — the non-clobbering schedule
  lemma: for a `Nodup`-dst schedule whose source is not an earlier dst,
  applying the schedule writes the source's *original* value to the dst.
* `breakOneCycle_swap_correct` (2-cycle), `breakOneCycle_3cycle_correct`,
  `breakOneCycle_4cycle_correct` — concrete cycle-rotation correctness.

## What's still open

For full general-case correctness:

1. **`walkEmits_sources_fresh`** — every source in `walkEmits` is not an
   earlier destination. This is the non-clobbering precondition required
   by `applySequentialL_at_dst_unique` to close the cycle proof. The
   missing piece is a *cycle precondition* on `es`: e.g.,
   `∀ s d, (s, d) ∈ es → ∃ s', (s', s) ∈ es` (every source has a writer).
   Under this hypothesis the walk cannot terminate via `srcOf? = none`;
   it must terminate via `source = start`, and in that case sources
   form a continuation of dsts that's all-Nodup.

2. **`breakOneCycle_sound`** — combine `walkEmits_dsts_nodup` +
   `walkEmits_sources_fresh` (via `applySequentialL_at_dst_unique`)
   with the `(start, tmp)` save and `(tmp, last)` restore wrappers to
   show breakOneCycle on a cycle rotates it correctly.

3. **`phase2_sound`** — phase-2 induction analogous to `phase1_sound`,
   draining each cycle in turn.

4. **`preprocess` correctness** — filtering self-copies and exact
   duplicates preserves `applyParallel`.

5. **Array↔List bridge for `sequenceParallelCopies`** — connecting the
   public `sequenceParallelCopies pairs` with the verified
   `sequenceParallelCopiesL pairs.toList`.

6. **`sequenceParallelCopies_correct`** — assembly of phase 1 + phase 2
   into `RealisesParallel sequenceParallelCopies`.
-/

namespace ParallelCopies

open Spec

/-! ## Top-level: empty input -/

@[simp] theorem sequenceParallelCopiesL_nil :
    sequenceParallelCopiesL [] = [] := by
  simp [sequenceParallelCopiesL, preprocess, phase1, phase2, smallestDst,
        findLeafEdge, List.foldl]

@[simp] theorem sequenceParallelCopies_empty :
    sequenceParallelCopies #[] = #[] := by
  simp [sequenceParallelCopies]

theorem sequenceParallelCopies_correct_on_empty
    (s : State) (r : UInt32) :
    applySequential (sequenceParallelCopies #[]) (lift s) (.given r) =
      applyParallel #[] s r := by
  simp

end ParallelCopies
