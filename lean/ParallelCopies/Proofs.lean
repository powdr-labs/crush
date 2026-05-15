import ParallelCopies.Phase2

/-!
# Algorithm-level proofs — final theorem

The full correctness statement, `sequenceParallelCopies_correct :
RealisesParallel sequenceParallelCopies`, lives at the bottom of this
file. It is axiom-clean: it depends only on `propext`, `Classical.choice`,
and `Quot.sound` — Lean's three foundational axioms. No `sorry`, no
`nativeDecide`, no native-code escape hatches.

## How the proof composes

The final proof rewrites the statement through six lemmas, each from a
single source module, in this order:

1. `applyParallel_eq_L`, `applySequential_eq_L` (`ListSpec.lean`) —
   translate Array-based spec to List-based mirror.
2. `sequenceParallelCopiesL_eq_explicit` (this file) — expose the
   `nonCycle ++ phase2` decomposition.
3. `applySequentialL_append` (`ListSpec.lean`) — split the sequential
   application along the `++`.
4. `phase2_sound` (`Phase2.lean`) with `acc = []` — phase 2's schedule on
   the post-nonCycle state matches the parallel block of the residual
   cycles.
5. `phase1_sound` (`Phase1.lean`) — phase 1's residual + emitted copies
   give the parallel block of the preprocessed input.
6. `applyParallelLS_preprocess_eq` (`Phase2.lean`) — preprocessing
   (drop self-copies and exact duplicates) preserves the parallel block.

The structural side-conditions (`UniqueDst`, no self-loops, `AllOnCycle`
for the residual) are supplied by `phase1_preserves_uniqueDst`,
`phase1_preserves_no_self`, `phase1_residual_allOnCycle`, and the
analogous preprocess lemmas.

For the catalogue of intermediate lemmas (cycle-walk machinery,
`cycleOf` disjointness, accumulator independence, etc.) see the per-file
docstrings in `Phase1.lean` and `Phase2.lean`; this file deliberately
stays short and only chains the top-level ingredients.
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
