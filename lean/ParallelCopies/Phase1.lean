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

/-! ## Strong membership characterisation of `peelStep` -/

/-- Every element of `peelStep s d es` either comes from an *unchanged*
    edge of `es` (whose source was not `s`) or from an edge `(s, x) ∈ es`
    with `x ≠ d` whose source was rewritten to `d`. -/
theorem mem_peelStep
    (s d : UInt32) (es : List Edge) (e : Edge) :
    e ∈ peelStep s d es →
      (e ∈ es ∧ e.1 ≠ s) ∨ (∃ x, (s, x) ∈ es ∧ x ≠ d ∧ e = (d, x)) := by
  induction es with
  | nil => intro h; cases h
  | cons e' rest ih =>
    simp only [peelStep]
    split
    · rename_i heq; subst heq
      intro h
      rcases ih h with ⟨h1, h2⟩ | ⟨x, h1, h2, h3⟩
      · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ h1, h2, h3⟩
    · split
      · rename_i hne_e'_sd hsrc
        obtain ⟨a, b⟩ := e'
        simp only at hsrc
        subst hsrc
        intro h
        rcases List.mem_cons.mp h with heq | hmem
        · refine Or.inr ⟨b, List.mem_cons_self, ?_, heq⟩
          intro h_b_eq_d
          subst h_b_eq_d
          exact hne_e'_sd rfl
        · rcases ih hmem with ⟨h1, h2⟩ | ⟨x, h1, h2, h3⟩
          · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
          · exact Or.inr ⟨x, List.mem_cons_of_mem _ h1, h2, h3⟩
      · rename_i _ hsrc
        intro h
        rcases List.mem_cons.mp h with heq | hmem
        · subst heq; exact Or.inl ⟨List.mem_cons_self, hsrc⟩
        · rcases ih hmem with ⟨h1, h2⟩ | ⟨x, h1, h2, h3⟩
          · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
          · exact Or.inr ⟨x, List.mem_cons_of_mem _ h1, h2, h3⟩

/-! ## `UniqueDst` preservation -/

theorem peelStep_uniqueDst
    (s d : UInt32) (es : List Edge)
    (hWF : UniqueDst es) :
    UniqueDst (peelStep s d es) := by
  intro src1 src2 dst h1 h2
  rcases mem_peelStep _ _ _ _ h1 with ⟨hr1, h1_src_ne⟩ | ⟨x1, hx1_mem, _, heq1⟩
  · rcases mem_peelStep _ _ _ _ h2 with ⟨hr2, _⟩ | ⟨x2, hx2_mem, _, heq2⟩
    · exact hWF src1 src2 dst hr1 hr2
    · have h_x2 : x2 = dst := by injection heq2 with _ h; exact h.symm
      rw [h_x2] at hx2_mem
      have : src1 = s := hWF src1 s dst hr1 hx2_mem
      exact absurd this h1_src_ne
  · rcases mem_peelStep _ _ _ _ h2 with ⟨hr2, h2_src_ne⟩ | ⟨x2, hx2_mem, _, heq2⟩
    · have h_x1 : x1 = dst := by injection heq1 with _ h; exact h.symm
      rw [h_x1] at hx1_mem
      have : src2 = s := hWF src2 s dst hr2 hx1_mem
      exact absurd this h2_src_ne
    · have h_a : src1 = d := by injection heq1 with h _
      have h_b : src2 = d := by injection heq2 with h _
      rw [h_a, h_b]

/-- `peelStep` preserves the "no self-loops" invariant.
    Source-swap turns `(s, x)` into `(d, x)`; this is a self-loop only if
    `d = x`, but `peelStep` drops `(s, d)` itself, so the only candidates
    `(s, x)` with `x ≠ d` remain non-self after swap. -/
theorem peelStep_no_self
    (s d : UInt32) (es : List Edge)
    (h : ∀ e ∈ es, e.1 ≠ e.2) :
    ∀ e ∈ peelStep s d es, e.1 ≠ e.2 := by
  induction es with
  | nil => intros e he; cases he
  | cons e' rest ih =>
    have h' : ∀ x ∈ rest, x.1 ≠ x.2 :=
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h_e' : e'.1 ≠ e'.2 := h e' List.mem_cons_self
    simp only [peelStep]
    split
    · -- e' = (s, d), dropped
      exact ih h'
    · split
      · -- e'.1 = s, swapped to (d, e'.2)
        rename_i hne_e'_sd hsrc
        intro x hx
        rcases List.mem_cons.mp hx with heq | hmem
        · -- x = (d, e'.2). Need d ≠ e'.2. If e'.2 = d, then (e'.1, e'.2) = (s, d). But hne_e'_sd.
          subst heq
          intro hcontra
          apply hne_e'_sd
          obtain ⟨a, b⟩ := e'
          simp only at hsrc
          subst hsrc
          simp only at hcontra
          simp [hcontra]
        · exact ih h' x hmem
      · -- e' kept unchanged
        intro x hx
        rcases List.mem_cons.mp hx with heq | hmem
        · subst heq; exact h_e'
        · exact ih h' x hmem

/-! ## `find?` after `peelStep` for non-peeled destinations -/

/-- For `r' ≠ d` and no self-loops, `find?` after `peelStep` is the
    source-swap-mapped `find?` of the original. -/
theorem find?_peelStep_ne
    (s d : UInt32) (es : List Edge) (r' : UInt32)
    (h_ne_dst : r' ≠ d) (h_no_self : ∀ e ∈ es, e.1 ≠ e.2) :
    (peelStep s d es).find? (Pair.appliesTo · r') =
      (es.find? (Pair.appliesTo · r')).map
        (fun e => if e.1 = s then (d, e.2) else e) := by
  induction es with
  | nil => simp [peelStep]
  | cons e rest ih =>
    have h_no_self' : ∀ e' ∈ rest, e'.1 ≠ e'.2 :=
      fun e' he' => h_no_self e' (List.mem_cons_of_mem _ he')
    have h_e_no_self : e.1 ≠ e.2 := h_no_self e List.mem_cons_self
    have ih' := ih h_no_self'
    simp only [peelStep]
    split
    · -- e = (s, d): dropped
      rename_i heq; subst heq
      have h_sd_not : Pair.appliesTo (s, d) r' = false := by
        rw [Pair.appliesTo_false_iff]; exact Or.inl (Ne.symm h_ne_dst)
      show (peelStep s d rest).find? (Pair.appliesTo · r') =
           ((match Pair.appliesTo (s, d) r' with
             | true => some (s, d)
             | false => List.find? (Pair.appliesTo · r') rest).map _)
      rw [h_sd_not, ih']
    · split
      · -- e ≠ (s, d), e.1 = s: swap to (d, e.2)
        rename_i hne hsrc
        show (match Pair.appliesTo (d, e.2) r' with
              | true => some (d, e.2)
              | false => List.find? (Pair.appliesTo · r') (peelStep s d rest)) =
             ((match Pair.appliesTo e r' with
               | true => some e
               | false => List.find? (Pair.appliesTo · r') rest).map _)
        by_cases h_app : e.2 = r'
        · -- e applies to r'. Need: peelStep's (d, e.2) also applies.
          have h_e_app : Pair.appliesTo e r' = true := by
            rw [Pair.appliesTo_iff]; exact ⟨h_app, h_e_no_self⟩
          have h_d_app : Pair.appliesTo (d, e.2) r' = true := by
            rw [Pair.appliesTo_iff]
            refine ⟨h_app, ?_⟩
            rw [h_app]; exact Ne.symm h_ne_dst
          rw [h_e_app, h_d_app]
          simp [hsrc]
        · have h_e_not : Pair.appliesTo e r' = false := by
            rw [Pair.appliesTo_false_iff]; exact Or.inl h_app
          have h_d_not : Pair.appliesTo (d, e.2) r' = false := by
            rw [Pair.appliesTo_false_iff]; exact Or.inl h_app
          rw [h_e_not, h_d_not, ih']
      · -- e ≠ (s, d), e.1 ≠ s: unchanged
        rename_i hne hsrc
        show (match Pair.appliesTo e r' with
              | true => some e
              | false => List.find? (Pair.appliesTo · r') (peelStep s d rest)) =
             ((match Pair.appliesTo e r' with
               | true => some e
               | false => List.find? (Pair.appliesTo · r') rest).map _)
        cases h_app : Pair.appliesTo e r' with
        | true =>
          -- find? returns some e; map applies if e.1 = s. We have e.1 ≠ s.
          simp [hsrc]
        | false => rw [ih']

/-! ## `peelStep_sound` at the peeled destination -/

/-- The key special case of `peelStep_sound` at `r = .given d`: the
    peeled edge `(s, d)` matches the parallel block's effect on `d`,
    namely writing `σ (.given s)` into `d`. -/
theorem peelStep_sound_at_d
    (s d : UInt32) (es : List Edge)
    (hWF : UniqueDst es) (h_mem : (s, d) ∈ es) (h_ne : s ≠ d) (σ : SState) :
    applyParallelLS es σ (.given d) =
      applyParallelLS (peelStep s d es) (step σ (.given s, .given d)) (.given d) := by
  show (match es.find? (Pair.appliesTo · d) with
        | some (src, _) => σ (.given src)
        | none          => σ (.given d)) =
       (match (peelStep s d es).find? (Pair.appliesTo · d) with
        | some (src, _) => step σ (.given s, .given d) (.given src)
        | none          => step σ (.given s, .given d) (.given d))
  rw [find?_dst_of_mem s d es hWF h_mem h_ne, find?_peelStep_self s d es hWF h_mem]
  simp [step]

/-! ## Full `peelStep_sound`: phase-1's local invariant -/

/-- Phase-1's central correctness lemma: emitting `(s, d)` and then taking
    the residual `peelStep s d es` as the parallel block on the updated
    sequential state is equivalent to the original parallel block. -/
theorem peelStep_sound
    (s d : UInt32) (es : List Edge)
    (hWF : UniqueDst es) (h_mem : (s, d) ∈ es) (h_ne : s ≠ d)
    (h_leaf : isLeaf d es = true)
    (h_no_self : ∀ e ∈ es, e.1 ≠ e.2)
    (σ : SState) :
    applyParallelLS es σ =
      applyParallelLS (peelStep s d es) (step σ (.given s, .given d)) := by
  funext r
  cases r with
  | temp =>
    -- temp register: neither side reads it from edges
    unfold applyParallelLS
    simp [step]
  | given r' =>
    by_cases h_eq : r' = d
    · rw [h_eq]
      exact peelStep_sound_at_d s d es hWF h_mem h_ne σ
    · -- r' ≠ d. Use find?_peelStep_ne.
      show (match es.find? (Pair.appliesTo · r') with
            | some (src, _) => σ (.given src)
            | none          => σ (.given r')) =
           (match (peelStep s d es).find? (Pair.appliesTo · r') with
            | some (src, _) => step σ (.given s, .given d) (.given src)
            | none          => step σ (.given s, .given d) (.given r'))
      rw [find?_peelStep_ne s d es r' h_eq h_no_self]
      cases hres : es.find? (Pair.appliesTo · r') with
      | none =>
        -- No writer for r'; both sides give σ (.given r')
        simp only [Option.map_none]
        -- RHS: step σ ... (.given r') where r' ≠ d
        have : step σ (.given s, .given d) (.given r') = σ (.given r') := by
          simp [step, Register.given.injEq, h_eq]
        rw [this]
      | some pair =>
        obtain ⟨s', t⟩ := pair
        have hfound := List.find?_eq_some_iff_append.mp hres
        have happ : Pair.appliesTo (s', t) r' = true := hfound.1
        rw [Pair.appliesTo_iff] at happ
        have hdst : t = r' := happ.1
        have hne_st : s' ≠ t := happ.2
        have h_mem' : (s', t) ∈ es := by
          obtain ⟨as, bs, hsplit, _⟩ := hfound.2
          rw [hsplit]; simp
        by_cases h_src_eq : s' = s
        · -- source-swap case: e becomes (d, t). step writes σ (.given s) at d.
          subst h_src_eq
          subst hdst
          simp [step]
        · -- unchanged. step at .given s' is identity (s' ≠ d).
          have h_s'_ne_d : s' ≠ d :=
            isLeaf_no_src h_leaf (s', t) h_mem'
          subst hdst
          simp [step, h_src_eq, h_s'_ne_d]

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
