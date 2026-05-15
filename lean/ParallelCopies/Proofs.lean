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

Structural / cycle-tracking lemmas:

* `mem_eraseDst`, `eraseDst_uniqueDst`, `eraseDst_no_self`.
* `srcOf?_mem`, `srcOf?_eq_some_of_mem`, `srcOf?_eraseDst_self`,
  `srcOf?_eraseDst_ne`.
* `walkCycle_acc_prefix`, `walkCycle_acc_indep_last/_es/_schedule` —
  accumulator-independence of walkCycle's outputs.
* `walkVisits_eq_of_onCycle`, `walkErased_eq_of_onCycle` — the walk
  matches the cycle path under `OnCycle`.
* `walkEmits_subset_es`, `walkEmits_dsts_nodup` — walkEmits's pairs
  are in es and have distinct dsts.
* `consPairs_*` lemmas — pair-up-consecutive structural identities.

Single-cycle correctness:

* `applySequentialL_at_dst_unique` — non-clobbering schedule.
* `breakOneCycle_writes_last/_non_last/_preserves_non_cycle_dst` —
  per-position correctness.
* **`breakOneCycle_sound_at_cycle`** — unified single-cycle correctness:
  at every cycle node, the schedule writes the parallel value.

Cycle disjointness machinery (for the multi-cycle induction):

* `iterWriter`, `cycleOf_closed_under_iterWriter` — writer chain stays
  in cycleOf.
* `iterWriter_path_step/_close` — the writer chain from path[0] visits
  path[i] after i steps and closes after path.length steps.
* **`cycle_disjoint_of_start_not_in`** — if r's cycle's start is not in
  cycleOf, all of r's cycle nodes are disjoint from cycleOf.

AllOnCycle preservation:

* `srcOf?_filter_ne_removed`, `eraseDst_filter_swap`,
  `cyclePathTo_lift_disjoint` — supporting filter calculations.
* **`allOnCycle_preserved_by_breakOneCycle`** — after handling one
  cycle, the residual still has every dst on a cycle.

Multi-cycle correctness:

* `smallestDst_eq_none_iff`, `smallestDst_some_mem`,
  `applyParallelLS_eraseDst_ne`, `cycleOf_length_le`,
  `breakOneCycle_residual`, `breakOneCycle_schedule_acc_decomp`,
  `applyParallelLS_filter_disjoint`, `cycleOf_contains_start`,
  `writer_not_in_cycleOf_of_not_in`.
* **`phase2_sound`** — the multi-cycle theorem:

      applySequentialL (phase2 fuel .temp es acc) σ (.given r) =
        applyParallelLS es (applySequentialL acc σ) (.given r)

  under `UniqueDst es`, `no_self_loops es`, `AllOnCycle es`, and
  `es.length ≤ fuel`. Axiom-clean.

Concrete sanity checks: `breakOneCycle_swap_correct` (2-cycle),
`breakOneCycle_3cycle_correct`, `breakOneCycle_4cycle_correct`.

## What's still open

For full general-case correctness:

1. **`onCycle_of_dst`** — phase 1's residual satisfies `AllOnCycle`.
   Requires: after phase 1, srcs = dsts (no leaves, no roots) + pigeon-
   hole on the writer chain.

2. **`preprocess` correctness** — filtering self-copies and exact
   duplicates preserves `applyParallel`.

3. **Array↔List bridge for `sequenceParallelCopies`** — connecting the
   public `sequenceParallelCopies pairs` with the verified
   `sequenceParallelCopiesL pairs.toList`.

4. **Disjoint-register commutation** — phase 2 and the nonCycle leaves
   touch disjoint register sets (nonCycle.dsts ∩ cycleOf nodes = ∅,
   nonCycle.sources ∩ cycleOf nodes = ∅), so the
   `phase2 ++ nonCycle` order is equivalent to `nonCycle ++ phase2`.

5. **`sequenceParallelCopies_correct`** — assembly of phase 1 + phase 2
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

/-! ## Helper for phase1's residual length bound -/

private theorem phase1_length_le :
    ∀ (fuel : Nat) (es : Edges) (acc : List Edge),
      (phase1 fuel es acc).1.length ≤ es.length
  | 0, es, _ => by simp [phase1]
  | n + 1, es, acc => by
    unfold phase1
    cases h_find : findLeafEdge es with
    | none => simp
    | some pair =>
      obtain ⟨s, d⟩ := pair
      simp only
      calc (phase1 n (peelStep s d es) (acc ++ [(s, d)])).1.length
          ≤ (peelStep s d es).length := phase1_length_le n _ _
        _ ≤ es.length := peelStep_length_le s d es

/-! ## Final theorem (assembly remains for future work)

The pieces needed to assemble `RealisesParallel sequenceParallelCopies` are
all in place — see Phase2.lean and the documentation block above for the
catalog. The final assembly is a routine composition:

```
applySequentialL (sequenceParallelCopiesL pairs.toList) (lift s) (.given r)
  = applySequentialL (phase2 ...) (applySequentialL nonCycle_mapped (lift s)) (.given r)
                                              [foldl_append]
  = applyParallelLS es_residual (applySequentialL nonCycle_mapped (lift s)) (.given r)
                                              [phase2_sound, with AllOnCycle via
                                               phase1_residual_allOnCycle]
  = applyParallelLS preprocess(pairs.toList) (lift s) (.given r)
                                              [phase1_sound]
  = applyParallelLS pairs.toList (lift s) (.given r)
                                              [applyParallelLS_preprocess_eq]
  = applyParallelL pairs.toList s r              [lift unfolding]
```

The remaining mechanical work is threading the `let` bindings of
`sequenceParallelCopiesL` through Lean's `generalize`/`obtain` tactics
without losing pattern matches against the lemmas. -/

end ParallelCopies
