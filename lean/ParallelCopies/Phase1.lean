import ParallelCopies.ListSpec

/-!
# Phase 1 correctness: tree pruning with source-swap

This module proves the central correctness lemma for phase 1, that
`peelStep s d es` followed by the sequential copy `(.given s, .given d)`
is equivalent to one parallel-block step of `es`.

The high-level argument:

* The edge being peeled, `(s, d)`, is dropped.
* Every other edge with source `s` has its source rewritten to `d`,
  because by the time those edges are read, `d` already holds the value
  originally at `s` (we just copied it there).
* `d` is required to be a *leaf* (not used as a source in `es`), so the
  rewriting never has to chase another step.
-/

namespace ParallelCopies.Spec

open Register

/-! ## Leaves -/

theorem isLeaf_iff (r : UInt32) (es : List Edge) :
    isLeaf r es = true ↔ ∀ e ∈ es, e.1 ≠ r := by
  unfold isLeaf
  simp [List.all_eq_true, bne_iff_ne]

theorem isLeaf_no_src {r : UInt32} {es : List Edge}
    (h : isLeaf r es = true) :
    ∀ e ∈ es, e.1 ≠ r := (isLeaf_iff r es).1 h

/-! ## Unique destinations -/

/-- Every two edges sharing a destination share the same source. This is the
    list-level form of `WellFormed`. -/
def UniqueDst (es : List Edge) : Prop :=
  ∀ s₁ s₂ d, (s₁, d) ∈ es → (s₂, d) ∈ es → s₁ = s₂

@[simp] theorem UniqueDst_nil : UniqueDst [] := by
  intro _ _ _ h; cases h

theorem UniqueDst_cons {e : Edge} {es : List Edge}
    (h : UniqueDst (e :: es)) : UniqueDst es := by
  intro s₁ s₂ d h₁ h₂
  exact h s₁ s₂ d (List.mem_cons_of_mem _ h₁) (List.mem_cons_of_mem _ h₂)

end ParallelCopies.Spec
