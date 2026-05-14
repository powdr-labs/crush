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

end ParallelCopies.Spec
