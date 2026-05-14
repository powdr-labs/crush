import ParallelCopies.Phase1

/-!
# Phase 2 correctness: breaking remaining cycles

After phase 1 the residual graph contains only pure cycles. This module
proves that `breakOneCycle` correctly schedules one such cycle, and that
`phase2` then iterates safely until the graph is empty.
-/

namespace ParallelCopies.Spec

open Register

/-! ## `eraseDst` characterisation -/

theorem mem_eraseDst (r : UInt32) (es : List Edge) (e : Edge) :
    e ∈ eraseDst r es ↔ e ∈ es ∧ e.2 ≠ r := by
  unfold eraseDst
  simp [bne_iff_ne]

theorem eraseDst_subset (r : UInt32) (es : List Edge) :
    ∀ e ∈ eraseDst r es, e ∈ es :=
  fun _ h => (mem_eraseDst _ _ _).mp h |>.1

/-- `eraseDst` preserves `UniqueDst`. -/
theorem eraseDst_uniqueDst (r : UInt32) (es : List Edge)
    (hWF : UniqueDst es) : UniqueDst (eraseDst r es) := by
  intro s1 s2 d h1 h2
  exact hWF s1 s2 d (eraseDst_subset _ _ _ h1) (eraseDst_subset _ _ _ h2)

/-- `eraseDst` preserves no-self-loops. -/
theorem eraseDst_no_self (r : UInt32) (es : List Edge)
    (h : ∀ e ∈ es, e.1 ≠ e.2) : ∀ e ∈ eraseDst r es, e.1 ≠ e.2 :=
  fun e he => h e (eraseDst_subset _ _ _ he)

/-! ## `srcOf?` characterisation -/

/-- If `srcOf?` returns `some s`, then `(s, r) ∈ es`. -/
theorem srcOf?_mem (es : List Edge) (r s : UInt32)
    (h : srcOf? r es = some s) : (s, r) ∈ es := by
  unfold srcOf? at h
  cases hf : es.find? (fun e => e.2 = r) with
  | none => simp [hf] at h
  | some pair =>
    rw [hf] at h
    simp at h
    obtain ⟨a, b⟩ := pair
    simp only at h
    have ⟨hpred, as, bs, hsplit, _⟩ := List.find?_eq_some_iff_append.mp hf
    simp at hpred
    subst hpred
    subst h
    rw [hsplit]
    simp

/-- After erasing the writer of `r`, looking up `r` again returns `none`,
    provided `es` had unique destinations. -/
theorem srcOf?_eraseDst_self
    (es : List Edge) (r : UInt32) :
    srcOf? r (eraseDst r es) = none := by
  unfold srcOf?
  have : (eraseDst r es).find? (fun e => e.2 = r) = none := by
    rw [List.find?_eq_none]
    intro e he
    have ⟨_, h_ne⟩ := (mem_eraseDst r es e).mp he
    simp [h_ne]
  rw [this]; rfl

end ParallelCopies.Spec
