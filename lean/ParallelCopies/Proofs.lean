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

/-! ## Final theorem -/

/-- Auxiliary form of `sequenceParallelCopiesL` that exposes the phase1 split. -/
private theorem sequenceParallelCopiesL_eq_explicit (pairs : List Edge) :
    sequenceParallelCopiesL pairs =
    (phase1 ((preprocess pairs).length + 1) (preprocess pairs) []).2.map
        (fun (s, d) => (Register.given s, Register.given d)) ++
      phase2 ((preprocess pairs).length + 1) Register.temp
        (phase1 ((preprocess pairs).length + 1) (preprocess pairs) []).1 [] := by
  unfold sequenceParallelCopiesL
  rfl

/-- The full correctness theorem. -/
theorem sequenceParallelCopies_correct :
    RealisesParallel sequenceParallelCopies := by
  intro pairs h_wf s r
  rw [applySequential_eq_L, applyParallel_eq_L]
  have h_arr_to_list : (sequenceParallelCopies pairs).toList =
      sequenceParallelCopiesL pairs.toList := by simp [sequenceParallelCopies]
  rw [h_arr_to_list, sequenceParallelCopiesL_eq_explicit]
  have h_wfL : WellFormedL pairs.toList :=
    fun s₁ s₂ d h_ne1 h_ne2 h_m1 h_m2 => h_wf s₁ s₂ d h_ne1 h_ne2 h_m1 h_m2
  have h_wf_pre : WellFormedL (preprocess pairs.toList) := preprocess_wellFormedL _ h_wfL
  have h_pre_uniq : UniqueDst (preprocess pairs.toList) := preprocess_uniqueDst _ h_wfL
  have h_pre_no_self : ∀ e ∈ preprocess pairs.toList, e.1 ≠ e.2 := preprocess_no_self _
  have h_pre_dsts_nodup : ((preprocess pairs.toList).map Prod.snd).Nodup :=
    preprocess_dsts_nodup _ h_wfL
  have h_es_uniq : UniqueDst (phase1 ((preprocess pairs.toList).length + 1)
                                (preprocess pairs.toList) []).1 :=
    phase1_preserves_uniqueDst _ _ _ h_pre_uniq
  have h_es_no_self : ∀ e ∈ (phase1 ((preprocess pairs.toList).length + 1)
                              (preprocess pairs.toList) []).1, e.1 ≠ e.2 :=
    phase1_preserves_no_self _ _ _ h_pre_no_self
  have h_es_fuel : (phase1 ((preprocess pairs.toList).length + 1)
                     (preprocess pairs.toList) []).1.length ≤
                   (preprocess pairs.toList).length + 1 := by
    have := phase1_length_le ((preprocess pairs.toList).length + 1)
      (preprocess pairs.toList) []
    omega
  have h_es_allOnCycle : AllOnCycle (phase1 ((preprocess pairs.toList).length + 1)
                                      (preprocess pairs.toList) []).1 :=
    phase1_residual_allOnCycle _ _ _ h_pre_uniq h_pre_dsts_nodup (by omega)
  -- Rewrite the lambda map to use edgeToCopy.
  have h_map_eq :
      (phase1 ((preprocess pairs.toList).length + 1)
        (preprocess pairs.toList) []).2.map
        (fun (x : Edge) => match x with | (s, d) => (Register.given s, Register.given d)) =
      (phase1 ((preprocess pairs.toList).length + 1)
        (preprocess pairs.toList) []).2.map edgeToCopy := by
    apply List.map_congr_left
    intro e _; obtain ⟨_, _⟩ := e; rfl
  rw [h_map_eq, applySequentialL_append]
  rw [phase2_sound _ _ [] _ h_es_uniq h_es_no_self h_es_allOnCycle h_es_fuel r]
  rw [applySequentialL_nil]
  -- Apply phase1_sound.
  have h_phase1_inv :
      applyParallelLS (preprocess pairs.toList) (lift s) =
      applyParallelLS (preprocess pairs.toList)
        (applySequentialL (([] : List Edge).map edgeToCopy) (lift s)) := by
    simp [applySequentialL]
  have h_phase1 :
      applyParallelLS (preprocess pairs.toList) (lift s) =
      applyParallelLS (phase1 ((preprocess pairs.toList).length + 1)
                        (preprocess pairs.toList) []).1
        (applySequentialL ((phase1 ((preprocess pairs.toList).length + 1)
                              (preprocess pairs.toList) []).2.map edgeToCopy) (lift s)) :=
    phase1_sound ((preprocess pairs.toList).length + 1) (preprocess pairs.toList) []
      (lift s) (preprocess pairs.toList) h_phase1_inv h_pre_uniq h_pre_no_self
  rw [← h_phase1]
  rw [applyParallelLS_preprocess_eq pairs.toList h_wfL (lift s) r]
  rfl

end ParallelCopies
