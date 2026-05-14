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

/-- After erasing the writer of `r`, looking up `r` again returns `none`. -/
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

/-- Erasing the writer of `r` leaves all other destinations unchanged. -/
theorem srcOf?_eraseDst_ne
    (es : List Edge) (r r' : UInt32) (h : r' ≠ r) :
    srcOf? r' (eraseDst r es) = srcOf? r' es := by
  unfold srcOf? eraseDst
  congr 1
  have h_sym : ¬ r = r' := fun heq => h heq.symm
  induction es with
  | nil => simp
  | cons e rest ih =>
    by_cases h_e_r : e.2 = r
    · have h_e_ne_r' : ¬ e.2 = r' := by
        intro heq
        rw [heq] at h_e_r
        exact h h_e_r
      simp [List.filter_cons, h_e_r, List.find?_cons, h_e_ne_r', ih, h_sym]
    · have h_keep : (e.2 != r) = true := by simp [h_e_r]
      by_cases h_e_r' : e.2 = r'
      · simp [List.filter_cons, h_keep, List.find?_cons, h_e_r', h]
      · simp [List.filter_cons, h_keep, List.find?_cons, h_e_r', ih, h]


/-! ## Basic structural properties of `walkCycle` -/

/-- `walkCycle` extends `acc` — it only appends new copies, never modifies
    existing ones. -/
theorem walkCycle_acc_prefix
    (fuel : Nat) (start curr : UInt32) (es : Edges)
    (acc : List (Register × Register)) :
    ∃ extra, (walkCycle fuel start curr es acc).2.2 = acc ++ extra := by
  induction fuel generalizing curr es acc with
  | zero => exact ⟨[], by simp [walkCycle]⟩
  | succ n ih =>
    unfold walkCycle
    split
    · exact ⟨[], by simp⟩
    · split
      · exact ⟨[], by simp⟩
      · rename_i source hsrc h_ne_start
        obtain ⟨extra, hex⟩ :=
          ih source (eraseDst curr es) (acc ++ [(.given source, .given curr)])
        refine ⟨(.given source, .given curr) :: extra, ?_⟩
        rw [hex]
        simp

/-- `walkCycle` only emits `given _ → given _` copies (no `temp`). -/
theorem walkCycle_emits_given
    (fuel : Nat) (start curr : UInt32) (es : Edges)
    (acc : List (Register × Register))
    (h_acc_given : ∀ cp ∈ acc, ∃ s d, cp = (.given s, .given d)) :
    ∀ cp ∈ (walkCycle fuel start curr es acc).2.2,
      ∃ s d, cp = (.given s, .given d) := by
  induction fuel generalizing curr es acc with
  | zero => intro cp hcp; exact h_acc_given cp hcp
  | succ n ih =>
    unfold walkCycle
    split
    · exact h_acc_given
    · split
      · exact h_acc_given
      · rename_i source hsrc _
        apply ih source (eraseDst curr es)
        intro cp hcp
        rcases List.mem_append.mp hcp with hcp | hcp
        · exact h_acc_given cp hcp
        · simp at hcp; subst hcp; exact ⟨source, curr, rfl⟩

/-! ## walkCycle emits a deterministic list of copies

The key insight: `walkCycle` produces a specific list of copies determined
by the walk path. We separate the *structural* aspect (what gets emitted)
from the *semantic* aspect (what the schedule does to the state). -/

/-- The list of `(source, curr)` pairs `walkCycle` emits. -/
def walkEmits : Nat → UInt32 → UInt32 → Edges → List (UInt32 × UInt32)
  | 0,    _,     _,    _  => []
  | n+1,  start, curr, es =>
    match srcOf? curr es with
    | none        => []
    | some source =>
      if source = start then []
      else (source, curr) :: walkEmits n start source (eraseDst curr es)

/-- `walkCycle`'s accumulator grows by exactly the `walkEmits` list. -/
theorem walkCycle_emits_eq
    (fuel : Nat) (start curr : UInt32) (es : Edges)
    (acc : List (Register × Register)) :
    (walkCycle fuel start curr es acc).2.2 =
      acc ++ (walkEmits fuel start curr es).map
        (fun e => (Register.given e.1, Register.given e.2)) := by
  induction fuel generalizing curr es acc with
  | zero => simp [walkCycle, walkEmits]
  | succ n ih =>
    unfold walkCycle walkEmits
    cases hsrc : srcOf? curr es with
    | none => simp
    | some source =>
      by_cases h : source = start
      · simp [h]
      · simp [h]
        rw [ih]
        simp

/-! ## Non-clobbering schedule lemma

A schedule is *non-clobbering at `d`* when:
* the destination `d` is written exactly once (unique-dst), and
* the source paired with `d` is not the destination of any copy *before*
  the `(s, d)` copy in the list.

Under these conditions, applying the schedule sequentially to `σ` leaves
`d` holding `σ s` — the *original* value at `s`, untouched by clobbering. -/

/-- A schedule that never writes to `r` leaves `r` unchanged. -/
theorem applySequentialL_preserves_non_dst
    (copies : List (Register × Register)) (σ : SState) (r : Register)
    (h : ∀ cp ∈ copies, cp.2 ≠ r) :
    applySequentialL copies σ r = σ r := by
  induction copies generalizing σ with
  | nil => simp
  | cons cp rest ih =>
    rw [applySequentialL_cons]
    have h_first : cp.2 ≠ r := h cp List.mem_cons_self
    have h_rest : ∀ cp' ∈ rest, cp'.2 ≠ r :=
      fun cp' hcp' => h cp' (List.mem_cons_of_mem _ hcp')
    rw [ih (step σ cp) h_rest, step_other σ cp (Ne.symm h_first)]

/-- The flagship non-clobbering lemma: when destinations are distinct
    (`Nodup`) and the source `s` is not the destination of any earlier
    copy, the final value at `d` is exactly `σ s`. -/
theorem applySequentialL_at_dst_unique
    (copies : List (Register × Register)) (σ : SState)
    (s d : Register)
    (h_mem : (s, d) ∈ copies)
    (h_unique : (copies.map Prod.snd).Nodup)
    (h_src_not_earlier_dst : ∀ pre post,
        copies = pre ++ (s, d) :: post →
        ∀ cp' ∈ pre, cp'.2 ≠ s) :
    applySequentialL copies σ d = σ s := by
  induction copies generalizing σ with
  | nil => simp at h_mem
  | cons cp rest ih =>
    rcases List.mem_cons.mp h_mem with heq | hmem'
    · -- cp is the unique writer
      subst heq
      rw [applySequentialL_cons]
      -- Since dsts are Nodup and cp = (s, d), rest has no (_, d).
      have h_rest_not_d : ∀ cp' ∈ rest, cp'.2 ≠ d := by
        intro cp' hcp' hdst
        have h_d_not_in : d ∉ rest.map Prod.snd := by
          simp only [List.map_cons, List.nodup_cons] at h_unique
          exact h_unique.1
        apply h_d_not_in
        rw [List.mem_map]
        exact ⟨cp', hcp', hdst⟩
      rw [applySequentialL_preserves_non_dst rest (step σ (s, d)) d h_rest_not_d]
      simp [step]
    · -- (s, d) is in rest. Apply IH.
      have h_unique' : (rest.map Prod.snd).Nodup := by
        simp only [List.map_cons, List.nodup_cons] at h_unique
        exact h_unique.2
      have h_fresh' : ∀ pre post,
          rest = pre ++ (s, d) :: post →
          ∀ cp' ∈ pre, cp'.2 ≠ s := by
        intro pre post h_split cp' hcp'
        exact h_src_not_earlier_dst (cp :: pre) post (by rw [h_split]; simp) cp'
          (List.mem_cons_of_mem _ hcp')
      have h_cp_not_s : cp.2 ≠ s := by
        obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem'
        exact h_src_not_earlier_dst (cp :: pre) post
          (by rw [hsplit]; simp) cp List.mem_cons_self
      rw [applySequentialL_cons, ih (step σ cp) hmem' h_unique' h_fresh',
          step_other σ cp (Ne.symm h_cp_not_s)]

/-! ## walkEmits structural invariants

For walkCycle to produce a correct non-clobbering schedule we need:
* destinations of `walkEmits` are pairwise distinct (Nodup);
* the source of each emit is not the destination of any earlier emit. -/

/-- Every destination in `walkEmits` matches the `curr` argument at its
    emission point — for our entry `walkCycle fuel start start es`, the
    first destination is `start`. -/
theorem walkEmits_dsts
    (fuel : Nat) (start curr : UInt32) (es : Edges) :
    (walkEmits fuel start curr es).map Prod.snd =
      match fuel, srcOf? curr es with
      | 0, _ => []
      | _, none => []
      | _, some source =>
        if source = start then []
        else curr :: (walkEmits (fuel - 1) start source (eraseDst curr es)).map Prod.snd := by
  cases fuel with
  | zero => simp [walkEmits]
  | succ n =>
    simp only [walkEmits]
    cases srcOf? curr es with
    | none => rfl
    | some source =>
      by_cases h : source = start
      · simp [h]
      · simp [h]

/-! ## walkEmits Nodup invariant

The destinations emitted by `walkCycle` are pairwise distinct because each
visit causes the visited register's edge to be erased, preventing future
walks from finding that register as a source again. -/

/-- Auxiliary version with a "visited so far" set `V`. -/
theorem walkEmits_dsts_nodup_aux
    (fuel : Nat) (start curr : UInt32) (es : Edges)
    (V : List UInt32)
    (h_V_erased : ∀ r ∈ V, srcOf? r es = none)
    (h_curr_not_in_V : curr ∉ V) :
    ((walkEmits fuel start curr es).map Prod.snd).Nodup ∧
    ∀ d ∈ (walkEmits fuel start curr es).map Prod.snd, d ∉ V := by
  induction fuel generalizing curr es V with
  | zero => simp [walkEmits]
  | succ n ih =>
    simp only [walkEmits]
    cases hsrc : srcOf? curr es with
    | none => simp
    | some source =>
      by_cases h_start : source = start
      · simp [h_start]
      · simp only [h_start, if_false, List.map_cons, List.nodup_cons, List.mem_cons]
        -- Want to apply IH with V' = V ++ [curr] and new_curr = source on (eraseDst curr es).
        -- Need: new V' is "erased", new curr ∉ V'.
        -- But source might be in V. Handle that case directly.
        have h_V'_erased : ∀ r ∈ curr :: V, srcOf? r (eraseDst curr es) = none := by
          intro r hr
          rcases List.mem_cons.mp hr with heq | hmem
          · rw [heq]; exact srcOf?_eraseDst_self es curr
          · have h_r_ne_curr : r ≠ curr := by
              intro heq; rw [heq] at hmem; exact h_curr_not_in_V hmem
            rw [srcOf?_eraseDst_ne _ _ _ h_r_ne_curr]
            exact h_V_erased r hmem
        by_cases h_src_in_V : source ∈ curr :: V
        · -- source ∈ V': srcOf? source (eraseDst curr es) = none, so recursion returns [].
          have h_src_erased : srcOf? source (eraseDst curr es) = none :=
            h_V'_erased source h_src_in_V
          have h_rec_empty :
              walkEmits n start source (eraseDst curr es) = [] := by
            cases n with
            | zero => rfl
            | succ m => simp [walkEmits, h_src_erased]
          rw [h_rec_empty]
          refine ⟨⟨?_, by simp⟩, ?_⟩
          · simp
          · intro d hd
            simp at hd
            subst hd
            exact h_curr_not_in_V
        · -- source ∉ V': apply IH.
          have h_new_curr_not_in_V' : source ∉ curr :: V := h_src_in_V
          have ⟨h_nodup, h_disj⟩ :=
            ih source (eraseDst curr es) (curr :: V) h_V'_erased h_new_curr_not_in_V'
          refine ⟨⟨?_, h_nodup⟩, ?_⟩
          · intro h_curr_in_rec
            have := h_disj curr h_curr_in_rec
            simp at this
          · intro d hd
            rcases hd with heq | hmem
            · subst heq; exact h_curr_not_in_V
            · have := h_disj d hmem
              simp at this
              exact this.2

/-- Top-level Nodup for walkEmits. -/
theorem walkEmits_dsts_nodup
    (fuel : Nat) (start curr : UInt32) (es : Edges) :
    ((walkEmits fuel start curr es).map Prod.snd).Nodup :=
  (walkEmits_dsts_nodup_aux fuel start curr es [] (by simp) (by simp)).1

/-! ## Concrete proof: breakOneCycle handles a swap (2-cycle) correctly -/

/-- For a 2-cycle `[(a, b), (b, a)]` with `a ≠ b`, `breakOneCycle`
    starting at `a` produces a schedule whose sequential application
    achieves the parallel swap effect on registers `a` and `b`. -/
theorem breakOneCycle_swap_correct
    (a b : UInt32) (hne : a ≠ b) (σ : SState) :
    let sched := (breakOneCycle 2 .temp a [(a, b), (b, a)] []).2
    applySequentialL sched σ (.given a) = σ (.given b) ∧
    applySequentialL sched σ (.given b) = σ (.given a) := by
  refine ⟨?_, ?_⟩ <;>
    (simp [breakOneCycle, walkCycle, srcOf?, List.find?, eraseDst,
           applySequentialL, step, hne, Ne.symm hne])

/-- For a 3-cycle `[(a, b), (b, c), (c, a)]` with all distinct registers,
    `breakOneCycle` starting at `a` produces a schedule whose sequential
    application achieves the parallel rotation `a ← c, b ← a, c ← b`. -/
theorem breakOneCycle_3cycle_correct
    (a b c : UInt32) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (σ : SState) :
    let sched := (breakOneCycle 3 .temp a [(a, b), (b, c), (c, a)] []).2
    applySequentialL sched σ (.given a) = σ (.given c) ∧
    applySequentialL sched σ (.given b) = σ (.given a) ∧
    applySequentialL sched σ (.given c) = σ (.given b) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp [breakOneCycle, walkCycle, srcOf?, List.find?, eraseDst,
           applySequentialL, step,
           hab, Ne.symm hab, hbc, Ne.symm hbc, hac, Ne.symm hac])

/-- For a 4-cycle, `breakOneCycle` produces the correct rotation. -/
theorem breakOneCycle_4cycle_correct
    (a b c d : UInt32)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (σ : SState) :
    let sched := (breakOneCycle 4 .temp a [(a, b), (b, c), (c, d), (d, a)] []).2
    applySequentialL sched σ (.given a) = σ (.given d) ∧
    applySequentialL sched σ (.given b) = σ (.given a) ∧
    applySequentialL sched σ (.given c) = σ (.given b) ∧
    applySequentialL sched σ (.given d) = σ (.given c) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp [breakOneCycle, walkCycle, srcOf?, List.find?, eraseDst,
           applySequentialL, step,
           hab, Ne.symm hab, hac, Ne.symm hac, had, Ne.symm had,
           hbc, Ne.symm hbc, hbd, Ne.symm hbd, hcd, Ne.symm hcd])

end ParallelCopies.Spec
