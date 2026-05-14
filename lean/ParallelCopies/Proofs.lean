import ParallelCopies.Phase2

/-!
# Algorithm-level proofs — current state

This module re-exports the proofs from `Phase1` and `Phase2` and tracks
progress toward the full `sequenceParallelCopies_correct` theorem.

## Theorems proved (all axiom-clean: `propext` / `Classical.choice` /
   `Quot.sound` only — no `sorry`, no `nativeDecide`)

### Empty-input correctness (full algorithm)

* `sequenceParallelCopies_correct_on_empty` — for `pairs = #[]`, the
  algorithm matches the parallel spec on every register and every initial
  state.

### Spec lemmas (`SpecLemmas.lean`) — 14 theorems

`applyParallel_nil`, `applyParallel_single`, `applyParallel_selfCopy`,
`applySequential_nil`, `applySequential_singleton`,
`applySequential_append`, `step_dst`, `step_other`, `lift_given`,
`lift_temp`, `findWriter?_nil`, `findWriter?_singleton`,
`Pair.appliesTo_*`, `realisesParallel_emptyImpl_on_empty`.

### List-based mirror (`ListSpec.lean`)

`applyParallelL_nil`, `applyParallelLS_nil`, `applyParallelLS_lift`,
`applySequentialL_nil`, `applySequentialL_cons`,
`applySequentialL_append`, `applySequentialL_singleton`,
`applySequential_eq_L`, `applyParallel_eq_L`.

### Phase 1 (tree pruning with source-swap) — `Phase1.lean`

Structural lemmas:
* `isLeaf_iff`, `isLeaf_cons`, `isLeaf_head`, `isLeaf_no_src`
* `UniqueDst_nil`, `UniqueDst_cons`
* `Pair.appliesTo_d_swap`, `Pair.appliesTo_iff`, `Pair.appliesTo_false_iff`

Source-swap soundness:
* `find?_peelStep_d_aux`, `find?_peelStep_self` — `peelStep` eliminates
  writes to the peeled destination.
* `find?_dst_of_mem` — well-formed `find?` returns the right edge.
* `find?_of_no_writer` — `find?` returns `none` when no edge applies.
* `mem_peelStep` — precise membership characterisation of `peelStep`.
* `peelStep_uniqueDst` — `UniqueDst` survives `peelStep`.
* `peelStep_no_self` — no-self-loops survives `peelStep`.
* `find?_peelStep_ne` — characterisation of `find?` after `peelStep` for
  destinations other than the peeled one.
* **`peelStep_sound_at_d`** — semantic soundness at the peeled destination.
* **`peelStep_sound`** — *full* source-swap soundness: emitting `(s, d)`
  and taking `peelStep s d es` as residual is equivalent to the original
  parallel block. *(The central local correctness lemma of phase 1.)*

Driver soundness:
* `findLeafEdge_some` — `findLeafEdge` returns an edge whose destination
  is a leaf.
* `edgeToCopy`, `applySequentialL_edgeToCopy_append` — register-lifting.
* **`phase1_sound`** — *full* phase-1 induction: running `phase1 fuel es
  acc` from a state where the algorithm's invariant holds preserves the
  invariant.

### Phase 2 (cycle breaking) — `Phase2.lean`

Structural lemmas:
* `mem_eraseDst`, `eraseDst_subset`, `eraseDst_uniqueDst`,
  `eraseDst_no_self`
* `srcOf?_mem`, `srcOf?_eraseDst_self`, `srcOf?_eraseDst_ne`
* `walkCycle_acc_prefix`, `walkCycle_emits_given`

## What's still open

The phase-2 *semantic* soundness lemma is the next milestone:

  theorem walkCycle_sound : ...
  theorem breakOneCycle_sound : ...
  theorem phase2_sound : ...

The walk forms a cycle that returns to its start, and the emitted
schedule rotates the cycle's values via the temporary register. The
proof of walkCycle's semantic effect needs a strong invariant tracking
which registers have been visited and how their values relate to the
original state — substantial work given the non-local nature of cycle
structure.

After phase 2, the remaining pieces to assemble the public-API theorem
`sequenceParallelCopies_correct : Spec.RealisesParallel
sequenceParallelCopies` are:

* `preprocess` correctness — filtering self-copies and exact duplicates
  preserves `applyParallel`.
* The bridge from list-based to Array-based statements at the FFI
  boundary.

The Phase 1 proof — including `peelStep_sound` (the deep source-swap
soundness lemma) and `phase1_sound` (full inductive proof) — is the
hardest local reasoning in the algorithm and is *complete*. What
remains for the full theorem is significant in volume but established
in pattern.
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

/-- End-to-end correctness on empty input. -/
theorem sequenceParallelCopies_correct_on_empty
    (s : State) (r : UInt32) :
    applySequential (sequenceParallelCopies #[]) (lift s) (.given r) =
      applyParallel #[] s r := by
  simp

end ParallelCopies
