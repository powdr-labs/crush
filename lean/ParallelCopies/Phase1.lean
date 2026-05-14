import ParallelCopies.ListSpec

/-!
# Phase 1 correctness: tree pruning with source-swap

This module proves the central correctness lemma for phase 1, that
`peelStep s d es` followed by the sequential copy `(.given s, .given d)`
is equivalent to one parallel-block step of `es`.
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

theorem isLeaf_cons {r : UInt32} {e : Edge} {es : List Edge}
    (h : isLeaf r (e :: es) = true) : isLeaf r es = true := by
  rw [isLeaf_iff] at h ⊢
  intro e' he'
  exact h e' (List.mem_cons_of_mem _ he')

theorem isLeaf_head {r : UInt32} {e : Edge} {es : List Edge}
    (h : isLeaf r (e :: es) = true) : e.1 ≠ r := by
  rw [isLeaf_iff] at h
  exact h e (List.mem_cons_self)

/-! ## Unique destinations -/

def UniqueDst (es : List Edge) : Prop :=
  ∀ s₁ s₂ d, (s₁, d) ∈ es → (s₂, d) ∈ es → s₁ = s₂

@[simp] theorem UniqueDst_nil : UniqueDst [] := by
  intro _ _ _ h; cases h

theorem UniqueDst_cons {e : Edge} {es : List Edge}
    (h : UniqueDst (e :: es)) : UniqueDst es := by
  intro s₁ s₂ d h₁ h₂
  exact h s₁ s₂ d (List.mem_cons_of_mem _ h₁) (List.mem_cons_of_mem _ h₂)

/-! ## `Pair.appliesTo` boolean identities -/

@[simp] theorem Pair.appliesTo_d_swap (d x : UInt32) :
    Pair.appliesTo (d, x) d = false := by
  simp only [Pair.appliesTo]
  by_cases h : x = d
  · subst h; simp
  · simp [h]

theorem Pair.appliesTo_iff (e : Edge) (r : UInt32) :
    Pair.appliesTo e r = true ↔ e.2 = r ∧ e.1 ≠ e.2 := by
  simp only [Pair.appliesTo, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]

theorem Pair.appliesTo_false_iff (e : Edge) (r : UInt32) :
    Pair.appliesTo e r = false ↔ e.2 ≠ r ∨ e.1 = e.2 := by
  rw [← Bool.not_eq_true, Pair.appliesTo_iff]
  constructor
  · intro h
    by_cases h2 : e.2 = r
    · refine Or.inr (Decidable.byContradiction fun h3 => h ⟨h2, h3⟩)
    · exact Or.inl h2
  · rintro (h | h) ⟨hdst, hne⟩
    · exact h hdst
    · exact hne h

/-! ## How `find?` interacts with `peelStep` for the peeled destination -/

/-- Local form: if the only possible source for `d` in `es` is `s`, then
    no edge in `peelStep s d es` writes to `d`. -/
theorem find?_peelStep_d_aux
    (s d : UInt32) (es : List Edge)
    (h : ∀ e ∈ es, e.2 = d → e.1 = s) :
    (peelStep s d es).find? (Pair.appliesTo · d) = none := by
  induction es with
  | nil => simp [peelStep]
  | cons e rest ih =>
    have h' : ∀ e' ∈ rest, e'.2 = d → e'.1 = s := fun e' he' hdst =>
      h e' (List.mem_cons_of_mem _ he') hdst
    simp only [peelStep]
    split
    · -- e = (s, d): drop
      exact ih h'
    · split
      · -- e.1 = s, source-swap to (d, e.2)
        rename_i hne_e_sd hsrc_eq_s
        simp only [List.find?, Pair.appliesTo_d_swap, cond_false]
        exact ih h'
      · -- unchanged
        rename_i hne_e_sd hsrc_ne_s
        have h_e2_ne : e.2 ≠ d := fun hcontra =>
          hsrc_ne_s (h e (List.mem_cons_self) hcontra)
        have h_app : Pair.appliesTo e d = false := by
          rw [Pair.appliesTo_false_iff]; exact Or.inl h_e2_ne
        simp only [List.find?, h_app, cond_false]
        exact ih h'

/-- After peeling the unique edge to `d`, no edge in the result writes to `d`. -/
theorem find?_peelStep_self
    (s d : UInt32) (es : List Edge)
    (hWF : UniqueDst es) (h_mem : (s, d) ∈ es) :
    (peelStep s d es).find? (Pair.appliesTo · d) = none := by
  apply find?_peelStep_d_aux
  intro e he hdst
  -- e ∈ es with e.2 = d means e = (e.1, d). Combined with (s, d) ∈ es and WF, e.1 = s.
  obtain ⟨a, b⟩ := e
  simp only at hdst
  subst hdst
  exact hWF a s _ he h_mem

/-! ## Finding the writer of a given destination in `es` -/

/-- In a well-formed graph, looking up the writer of `d` returns the edge
    `(s, d)` whenever `(s, d) ∈ es` and the pair is non-self. -/
theorem find?_dst_of_mem
    (s d : UInt32) (es : List Edge)
    (hWF : UniqueDst es) (h_mem : (s, d) ∈ es) (h_ne : s ≠ d) :
    es.find? (Pair.appliesTo · d) = some (s, d) := by
  induction es with
  | nil => simp at h_mem
  | cons e rest ih =>
    have hWF' : UniqueDst rest := UniqueDst_cons hWF
    have h_sne : (s != d) = true := bne_iff_ne.mpr h_ne
    rcases List.mem_cons.mp h_mem with heq | hmem'
    · -- e = (s, d): first edge is a match
      subst heq
      simp [List.find?_cons, Pair.appliesTo, h_sne]
    · -- (s, d) ∈ rest
      by_cases hap_e : Pair.appliesTo e d = true
      · rw [Pair.appliesTo_iff] at hap_e
        obtain ⟨hdst, _⟩ := hap_e
        obtain ⟨a, b⟩ := e
        simp only at hdst; subst hdst
        have ha : a = s := hWF a s _ List.mem_cons_self (List.mem_cons_of_mem _ hmem')
        subst ha
        simp [List.find?_cons, Pair.appliesTo, h_sne]
      · have hap_false : Pair.appliesTo e d = false := by
          cases h : Pair.appliesTo e d with
          | true => exact absurd h hap_e
          | false => rfl
        show (match Pair.appliesTo e d with
              | true => some e
              | false => List.find? (Pair.appliesTo · d) rest) = some (s, d)
        rw [hap_false]
        exact ih hWF' hmem'

/-- The contrapositive form: if no edge in `es` writes to `r`, then
    `find?` returns `none`. -/
theorem find?_of_no_writer
    (es : List Edge) (r : UInt32)
    (h : ∀ e ∈ es, ¬ (e.2 = r ∧ e.1 ≠ e.2)) :
    es.find? (Pair.appliesTo · r) = none := by
  induction es with
  | nil => simp [List.find?]
  | cons e rest ih =>
    have h' : ∀ e' ∈ rest, ¬ (e'.2 = r ∧ e'.1 ≠ e'.2) :=
      fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have hap : Pair.appliesTo e r = false := by
      rw [Pair.appliesTo_false_iff]
      by_cases hdst : e.2 = r
      · refine Or.inr (Decidable.byContradiction fun hne =>
          h e List.mem_cons_self ⟨hdst, hne⟩)
      · exact Or.inl hdst
    show (match Pair.appliesTo e r with
          | true => some e
          | false => List.find? (Pair.appliesTo · r) rest) = none
    rw [hap]
    exact ih h'

end ParallelCopies.Spec
