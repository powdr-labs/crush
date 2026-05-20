import ParallelCopies.Spec
import ParallelCopies.Preprocess

/-!
# Stage 0 — spec lemmas

Algebraic facts about `applyParallel`, `applySequential`, `FunUpdate`, and
`sourceOf`. Independent of the actual algorithm.

The headline result here is `applyParallel_preprocess`: `preprocess` is a
no-op at the parallel-block level on `WellFormed` inputs. That lets the
correctness proof reason about `preprocess pairs` (which has the algorithm's
clean invariants) while still answering questions about `pairs`.
-/

namespace ParallelCopies.Spec

open Register

/-! ## `FunUpdate` -/

@[simp] theorem FunUpdate_apply_eq {α β} [DecidableEq α]
    (f : α → β) (a : α) (b : β) : FunUpdate f a b a = b := by
  simp [FunUpdate]

theorem FunUpdate_apply_ne {α β} [DecidableEq α]
    (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
    FunUpdate f a b x = f x := by
  simp [FunUpdate, h]

/-! ## `applySequential` factored through `Array.foldl`

`applySequential` is a do-block with two `let mut` variables. Lean's `for`-
desugaring puts both mutables into an `MProd Memory UInt32` and runs `forIn`
in the `Id` monad. We factor that through an explicit step function so we
can reason via `Array.foldl_append` / `Array.foldl_push`. -/

/-- One step of the sequential interpreter, expressed as a pure
    state-transformer on `(mem, tmp)`. -/
def applySeqStep (cp : Register × Register) (r : MProd Memory UInt32) :
    MProd Memory UInt32 :=
  let v := match cp.1 with
    | .temp     => r.snd
    | .given r' => r.fst r'
  match cp.2 with
    | .temp     => ⟨r.fst, v⟩
    | .given r' => ⟨FunUpdate r.fst r' v, r.snd⟩

/-- Stateful version of `applySequential`, returning both `(mem, tmp)`. -/
def applySeqState (r : MProd Memory UInt32) (xs : Array (Register × Register)) :
    MProd Memory UInt32 :=
  xs.foldl (fun r x => applySeqStep x r) r

/-- Helper: the `forIn` body inside `applySequential` factors through
    `applySeqStep`. -/
private theorem forIn_body_eq {α β : Type _} {m : Type _ → Type _} [Monad m]
    {xs : Array α} {init : β}
    {f g : α → β → m (ForInStep β)} (h : f = g) :
    forIn xs init f = forIn xs init g := by
  rw [h]

theorem applySequential_eq_state
    (tmp : UInt32) (copies : Array (Register × Register)) (mem : Memory) :
    applySequential tmp copies mem = (applySeqState ⟨mem, tmp⟩ copies).fst := by
  simp only [applySequential, Id.run, bind_pure_comp, map_pure]
  rw [forIn_body_eq (g := fun x r =>
        (pure (ForInStep.yield (applySeqStep x r)) : Id _))]
  · simp only [Array.forIn_pure_yield_eq_foldl]; rfl
  · funext x r
    unfold applySeqStep
    cases x.snd <;> rfl

@[simp] theorem applySeqState_empty (r : MProd Memory UInt32) :
    applySeqState r #[] = r := by
  simp [applySeqState]

theorem applySeqState_append (r : MProd Memory UInt32)
    (a b : Array (Register × Register)) :
    applySeqState r (a ++ b) = applySeqState (applySeqState r a) b := by
  simp [applySeqState]

theorem applySeqState_push (r : MProd Memory UInt32)
    (a : Array (Register × Register)) (cp : Register × Register) :
    applySeqState r (a.push cp) = applySeqStep cp (applySeqState r a) := by
  simp [applySeqState]

@[simp] theorem applySequential_empty (tmp : UInt32) (mem : Memory) :
    applySequential tmp #[] mem = mem := by
  rw [applySequential_eq_state]
  simp

/-! ## `applyParallel` and `sourceOf` -/

@[simp] theorem applyParallel_empty (mem : Memory) :
    applyParallel #[] mem = mem := by
  funext addr; simp [applyParallel, sourceOf]

theorem sourceOf_isSome_iff (pairs : Array (UInt32 × UInt32)) (d : UInt32) :
    (sourceOf pairs d).isSome ↔ ∃ s, (s, d) ∈ pairs ∧ s ≠ d := by
  unfold sourceOf
  refine ⟨?_, ?_⟩
  · intro h
    cases hfind : pairs.find? (fun e => e.2 == d && e.1 != e.2) with
    | none => simp_all
    | some p =>
      obtain ⟨s, d'⟩ := p
      have hp := Array.find?_some hfind
      have hmem := Array.mem_of_find?_eq_some hfind
      simp at hp
      obtain ⟨rfl, hne⟩ := hp
      exact ⟨s, hmem, hne⟩
  · intro ⟨s, hmem, hne⟩
    have hsome : (pairs.find? (fun e => e.2 == d && e.1 != e.2)).isSome := by
      rw [Array.find?_isSome]; exact ⟨(s, d), hmem, by simp [hne]⟩
    cases hfind : pairs.find? (fun e => e.2 == d && e.1 != e.2) with
    | none => simp_all
    | some p => cases p; simp

theorem sourceOf_eq_none_iff (pairs : Array (UInt32 × UInt32)) (d : UInt32) :
    sourceOf pairs d = none ↔ ∀ s, ¬ ((s, d) ∈ pairs ∧ s ≠ d) := by
  refine ⟨?_, ?_⟩
  · intro h s ⟨hmem, hne⟩
    have hsome : (sourceOf pairs d).isSome :=
      (sourceOf_isSome_iff pairs d).mpr ⟨s, hmem, hne⟩
    simp_all
  · intro h
    cases hs : sourceOf pairs d with
    | none => rfl
    | some s =>
      exfalso
      have hsome : (sourceOf pairs d).isSome := by rw [hs]; rfl
      obtain ⟨s', hmem, hne⟩ := (sourceOf_isSome_iff pairs d).mp hsome
      exact h s' ⟨hmem, hne⟩

/-! ## `preprocess` preserves `applyParallel`

For `WellFormed pairs`, `sourceOf` agrees on `pairs` and `preprocess pairs`
because (i) `preprocess` keeps every non-self edge of `pairs`
(`preprocess_complete`), and (ii) the well-formedness invariant pins the
source of any destination to a unique value, so the `find?` order doesn't
matter. -/

theorem wellFormed_preprocess (pairs : Array (UInt32 × UInt32))
    (h_wf : WellFormed pairs) : WellFormed (preprocess pairs) := by
  intro s₁ s₂ d h₁ h₂ h₁mem h₂mem
  exact h_wf s₁ s₂ d h₁ h₂
    (preprocess_subset pairs _ h₁mem) (preprocess_subset pairs _ h₂mem)

theorem sourceOf_preprocess (pairs : Array (UInt32 × UInt32))
    (h_wf : WellFormed pairs) (d : UInt32) :
    sourceOf (preprocess pairs) d = sourceOf pairs d := by
  cases h : sourceOf pairs d with
  | none =>
    rw [sourceOf_eq_none_iff] at h ⊢
    intro s ⟨hmem, hne⟩
    exact h s ⟨preprocess_subset pairs _ hmem, hne⟩
  | some s =>
    have hcorr := (sourceOf_correct pairs h_wf s d).mp h
    have hcorr' :=
      (sourceOf_correct (preprocess pairs) (wellFormed_preprocess pairs h_wf)
        s d).mpr
        ⟨preprocess_complete pairs _ hcorr.1 hcorr.2, hcorr.2⟩
    exact hcorr'

theorem applyParallel_preprocess (pairs : Array (UInt32 × UInt32))
    (h_wf : WellFormed pairs) (mem : Memory) :
    applyParallel (preprocess pairs) mem = applyParallel pairs mem := by
  funext addr
  unfold applyParallel
  rw [sourceOf_preprocess pairs h_wf addr]

end ParallelCopies.Spec
