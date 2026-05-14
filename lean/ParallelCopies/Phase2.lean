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

/-! ## Forward-reachability in an edge list

`ForwardPath es x y` says we can walk from `x` to `y` along edges in `es`,
following each edge in its natural direction. -/

inductive ForwardPath (es : Edges) : UInt32 → UInt32 → Prop where
  | refl  : ∀ x, ForwardPath es x x
  | step  : ∀ {x y z}, (x, y) ∈ es → ForwardPath es y z → ForwardPath es x z

@[simp] theorem ForwardPath.refl_self (es : Edges) (x : UInt32) :
    ForwardPath es x x := ForwardPath.refl x

/-- Forward paths compose. -/
theorem ForwardPath.trans
    {es : Edges} {x y z : UInt32}
    (h1 : ForwardPath es x y) (h2 : ForwardPath es y z) :
    ForwardPath es x z := by
  induction h1 with
  | refl _ => exact h2
  | step h_e _ ih => exact ForwardPath.step h_e (ih h2)

/-- Single-edge path. -/
theorem ForwardPath.single
    {es : Edges} {x y : UInt32} (h : (x, y) ∈ es) :
    ForwardPath es x y := ForwardPath.step h (ForwardPath.refl y)

/-- If `x ≠ y` and there's a forward path from `x` to `y`, then there's
    some first edge out of `x`. -/
theorem ForwardPath.step_inv
    {es : Edges} {x y : UInt32}
    (h : ForwardPath es x y) (hne : x ≠ y) :
    ∃ z, (x, z) ∈ es ∧ ForwardPath es z y := by
  cases h with
  | refl _ => exact absurd rfl hne
  | step h_e h_rest => exact ⟨_, h_e, h_rest⟩

/-! ## `ForwardPath` interacts cleanly with `eraseDst` -/

/-- A forward path from `x` to `y` where `y` is the only "absorbing" register
    (i.e., we don't pass through `r` along the way) survives erasing `r`'s
    incoming edges, provided `y ≠ r`. -/
theorem ForwardPath.of_eraseDst
    {es : Edges} {x y r : UInt32}
    (h : ForwardPath (eraseDst r es) x y) :
    ForwardPath es x y := by
  induction h with
  | refl _ => exact ForwardPath.refl _
  | step h_e _ ih =>
    have : _ ∈ es := ((mem_eraseDst _ _ _).mp h_e).1
    exact ForwardPath.step this ih

/-! ## Cycle traversal: walkCycle's full visit sequence

The list of registers `walkCycle` visits in order (including the initial
`curr`). This is `walkEmits.map Prod.snd` extended with the source of the
final emit — i.e., the full reverse-direction walk path. -/

/-- All registers visited by walkCycle, in walk order. The last element is
    the `curr` value when walkCycle terminates. -/
def walkVisits (fuel : Nat) (start curr : UInt32) (es : Edges) : List UInt32 :=
  match fuel with
  | 0 => [curr]
  | n+1 =>
    match srcOf? curr es with
    | none => [curr]
    | some source =>
      if source = start then [curr]
      else curr :: walkVisits n start source (eraseDst curr es)

@[simp] theorem walkVisits_zero (start curr : UInt32) (es : Edges) :
    walkVisits 0 start curr es = [curr] := rfl

@[simp] theorem walkVisits_head_eq
    (fuel : Nat) (start curr : UInt32) (es : Edges) :
    (walkVisits fuel start curr es).head? = some curr := by
  cases fuel with
  | zero => simp [walkVisits]
  | succ n =>
    unfold walkVisits
    cases srcOf? curr es with
    | none => simp
    | some source =>
      by_cases h : source = start
      · simp [h]
      · simp [h]

theorem walkVisits_ne_nil
    (fuel : Nat) (start curr : UInt32) (es : Edges) :
    walkVisits fuel start curr es ≠ [] := by
  cases fuel with
  | zero => simp [walkVisits]
  | succ n =>
    unfold walkVisits
    cases srcOf? curr es with
    | none => simp
    | some source =>
      by_cases h : source = start
      · simp [h]
      · simp [h]

/-- walkEmits's destinations are exactly the *initial portion* of
    walkVisits — every visit except the last gets its edge emitted. -/
theorem walkEmits_dsts_eq_walkVisits_init
    (fuel : Nat) (start curr : UInt32) (es : Edges) :
    (walkEmits fuel start curr es).map Prod.snd =
      (walkVisits fuel start curr es).dropLast := by
  induction fuel generalizing curr es with
  | zero => simp [walkEmits, walkVisits]
  | succ n ih =>
    unfold walkEmits walkVisits
    cases hsrc : srcOf? curr es with
    | none => simp
    | some source =>
      by_cases h : source = start
      · simp [h]
      · simp only [h, if_false, List.map_cons, ih]
        rw [List.dropLast_cons_of_ne_nil (walkVisits_ne_nil _ _ _ _)]

/-- The head of walkVisits is always `curr`. -/
theorem walkVisits_head_cons
    (fuel : Nat) (start curr : UInt32) (es : Edges) :
    ∃ rest, walkVisits fuel start curr es = curr :: rest := by
  cases fuel with
  | zero => exact ⟨[], rfl⟩
  | succ n =>
    unfold walkVisits
    cases srcOf? curr es with
    | none => exact ⟨[], rfl⟩
    | some source =>
      by_cases h : source = start
      · simp [h]
      · simp [h]

/-- walkEmits's sources are the *tail* of walkVisits — each step's source
    becomes the next visit. -/
theorem walkEmits_srcs_eq_walkVisits_tail
    (fuel : Nat) (start curr : UInt32) (es : Edges) :
    (walkEmits fuel start curr es).map Prod.fst =
      (walkVisits fuel start curr es).tail := by
  induction fuel generalizing curr es with
  | zero => simp [walkEmits, walkVisits]
  | succ n ih =>
    unfold walkEmits walkVisits
    cases hsrc : srcOf? curr es with
    | none => simp
    | some source =>
      by_cases h : source = start
      · simp [h]
      · simp only [h, if_false, List.map_cons, List.tail_cons, ih]
        obtain ⟨rest, hrest⟩ :=
          walkVisits_head_cons n start source (eraseDst curr es)
        rw [hrest]
        simp

/-! ## Cycle precondition

`CyclePathTo start es path` says `path` is a sequence of `srcOf?`-steps
ending at `start`: each consecutive pair `(curr, next)` in `path`
satisfies `srcOf? curr es = some next`, and the last register's
`srcOf?` returns `start`. This is exactly the walk that `walkCycle`
performs when it terminates via `source = start`. -/

inductive CyclePathTo (start : UInt32) : Edges → List UInt32 → Prop where
  | last  : ∀ {es curr}, srcOf? curr es = some start →
            CyclePathTo start es [curr]
  | step  : ∀ {es curr next rest}, srcOf? curr es = some next →
            next ≠ start →
            CyclePathTo start (eraseDst curr es) (next :: rest) →
            CyclePathTo start es (curr :: next :: rest)

/-- `start` is on a `srcOf?`-cycle in `es`. -/
def OnCycle (start : UInt32) (es : Edges) : Prop :=
  ∃ path, path ≠ [] ∧ path.head? = some start ∧ path.Nodup ∧
    CyclePathTo start es path

/-! ## walkVisits matches CyclePathTo's path -/

/-- If there is a `CyclePathTo` from `curr`, then `walkVisits` with enough
    fuel returns exactly that path. -/
theorem walkVisits_eq_of_cyclePathTo
    {path : List UInt32} {start : UInt32} {es : Edges}
    (hpath : CyclePathTo start es path)
    {fuel : Nat} (h_fuel : path.length ≤ fuel)
    {curr : UInt32} (h_head : path.head? = some curr) :
    walkVisits fuel start curr es = path := by
  induction hpath generalizing fuel curr with
  | last h_close =>
    rename_i es' curr_path
    simp at h_head
    subst h_head
    cases fuel with
    | zero => simp at h_fuel
    | succ n =>
      unfold walkVisits
      rw [h_close]
      simp
  | step h_step h_ne_start _ ih =>
    rename_i es' curr_path next rest _
    simp at h_head
    subst h_head
    cases fuel with
    | zero => simp at h_fuel
    | succ n =>
      have h_fuel' : (next :: rest).length ≤ n := by
        simp at h_fuel ⊢
        omega
      unfold walkVisits
      rw [h_step]
      simp [h_ne_start]
      exact ih h_fuel' rfl

/-- Under `OnCycle`, walkVisits returns the cycle's path. -/
theorem walkVisits_eq_of_onCycle
    (start : UInt32) (es : Edges)
    (hC : OnCycle start es)
    (fuel : Nat) (h_fuel : hC.choose.length ≤ fuel) :
    walkVisits fuel start start es = hC.choose := by
  obtain ⟨h_ne, h_head, h_nodup, h_path⟩ := hC.choose_spec
  exact walkVisits_eq_of_cyclePathTo h_path h_fuel h_head

/-- `walkVisits` is `Nodup` under `OnCycle`. -/
theorem walkVisits_nodup_of_onCycle
    (start : UInt32) (es : Edges)
    (hC : OnCycle start es)
    (fuel : Nat) (h_fuel : hC.choose.length ≤ fuel) :
    (walkVisits fuel start start es).Nodup := by
  rw [walkVisits_eq_of_onCycle start es hC fuel h_fuel]
  exact hC.choose_spec.2.2.1

/-! ## Sources of walkEmits are not the start

If `walkCycle` emits `(s, d)`, then `s ≠ start` — because the algorithm
stops *before* emitting when it would emit a copy whose source is `start`. -/

theorem walkEmits_sources_ne_start
    (fuel : Nat) (start curr : UInt32) (es : Edges) :
    ∀ cp ∈ walkEmits fuel start curr es, cp.1 ≠ start := by
  induction fuel generalizing curr es with
  | zero => simp [walkEmits]
  | succ n ih =>
    simp only [walkEmits]
    cases hsrc : srcOf? curr es with
    | none => simp
    | some source =>
      by_cases h_start : source = start
      · simp [h_start]
      · intro cp hcp
        simp only [h_start, if_false, List.mem_cons] at hcp
        rcases hcp with heq | hmem
        · subst heq; exact h_start
        · exact ih source (eraseDst curr es) cp hmem

/-! ## Non-clobbering of walkEmits under walkVisits.Nodup

By construction `walkEmits = consPairs walkVisits`, and we prove
non-clobbering by induction on the cycle path (which is what
walkVisits matches under `OnCycle`). -/

/-- Pair each consecutive pair as `(next, current)` for a list. -/
def consPairs : List UInt32 → List (UInt32 × UInt32)
  | []           => []
  | [_]          => []
  | a :: b :: rs => (b, a) :: consPairs (b :: rs)

@[simp] theorem consPairs_nil : consPairs [] = [] := rfl

@[simp] theorem consPairs_single (a : UInt32) : consPairs [a] = [] := rfl

theorem walkEmits_eq_consPairs_walkVisits
    (fuel : Nat) (start curr : UInt32) (es : Edges) :
    walkEmits fuel start curr es = consPairs (walkVisits fuel start curr es) := by
  induction fuel generalizing curr es with
  | zero => simp [walkEmits, walkVisits, consPairs]
  | succ n ih =>
    unfold walkEmits walkVisits
    cases hsrc : srcOf? curr es with
    | none => simp [consPairs]
    | some source =>
      by_cases h : source = start
      · simp [h, consPairs]
      · simp only [h, if_false]
        rw [ih]
        -- walkVisits returns curr :: rest where rest starts with source.
        obtain ⟨rest, hrest⟩ := walkVisits_head_cons n start source (eraseDst curr es)
        rw [hrest]
        simp [consPairs]

/-- consPairs's sources are exactly the tail of the input list. -/
theorem consPairs_sources_eq_tail (xs : List UInt32) :
    (consPairs xs).map Prod.fst = xs.tail := by
  match xs with
  | [] => simp [consPairs]
  | [_] => simp [consPairs]
  | a :: b :: rest =>
    simp only [consPairs, List.map_cons, List.tail_cons]
    have := consPairs_sources_eq_tail (b :: rest)
    simp only [List.tail_cons] at this
    rw [this]

/-- For a Nodup list, `consPairs` produces a schedule where no source is
    an earlier dst. -/
theorem consPairs_non_clobbering
    (xs : List UInt32) (h_nodup : xs.Nodup) :
    ∀ pre s d post, consPairs xs = pre ++ (s, d) :: post →
      ∀ cp' ∈ pre, cp'.2 ≠ s := by
  induction xs with
  | nil => simp [consPairs]
  | cons a rest ih =>
    cases rest with
    | nil => simp [consPairs]
    | cons b rest' =>
      simp only [consPairs]
      intro pre s d post hsplit cp' hcp' hcontra
      rw [List.nodup_cons] at h_nodup
      obtain ⟨ha_notin, h_rest_nodup⟩ := h_nodup
      cases pre with
      | nil => simp at hcp'
      | cons p pre' =>
        rw [List.cons_append, List.cons.injEq] at hsplit
        obtain ⟨hp_eq_ba, htail⟩ := hsplit
        -- hp_eq_ba : (b, a) = p. So p = (b, a).
        rw [← hp_eq_ba] at hcp'
        rcases List.mem_cons.mp hcp' with hp_eq | hp_in
        · -- cp' = (b, a). cp'.2 = a. hcontra: a = s. Goal: False.
          subst hp_eq
          have h_srcs_eq :
              (consPairs (b :: rest')).map Prod.fst = rest' := by
            have := consPairs_sources_eq_tail (b :: rest')
            simp [List.tail_cons] at this
            exact this
          have h_s_in_srcs : s ∈ (consPairs (b :: rest')).map Prod.fst := by
            rw [htail]
            rw [List.mem_map]
            exact ⟨(s, d), List.mem_append.mpr (Or.inr List.mem_cons_self), rfl⟩
          rw [h_srcs_eq] at h_s_in_srcs
          have h_a_in_rest' : a ∈ rest' := by
            simp at hcontra
            rw [hcontra]
            exact h_s_in_srcs
          exact ha_notin (List.mem_cons_of_mem _ h_a_in_rest')
        · exact ih h_rest_nodup pre' s d post htail cp' hp_in hcontra

/-- The non-clobbering condition for `walkEmits` under walkVisits.Nodup. -/
theorem walkEmits_non_clobbering
    (fuel : Nat) (start curr : UInt32) (es : Edges)
    (h_nodup : (walkVisits fuel start curr es).Nodup) :
    ∀ pre s d post, walkEmits fuel start curr es = pre ++ (s, d) :: post →
      ∀ cp' ∈ pre, cp'.2 ≠ s := by
  rw [walkEmits_eq_consPairs_walkVisits]
  exact consPairs_non_clobbering _ h_nodup

/-- Nodup is preserved by mapping `Register.given`. -/
theorem map_nodup_given (xs : List UInt32) (h : xs.Nodup) :
    (xs.map Register.given).Nodup := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih h.2⟩
    intro hcontra
    rw [List.mem_map] at hcontra
    obtain ⟨x, hx, hfx⟩ := hcontra
    have : x = a := by injection hfx
    subst this
    exact h.1 hx

/-! ## walkEmits writes the right values under OnCycle -/

/-- For each `(s, d)` in `walkEmits`, the register-tagged schedule writes
    `σ (.given s)` into `(.given d)` — the original-source value, intact. -/
theorem walkEmits_regify_writes
    (fuel : Nat) (start curr : UInt32) (es : Edges)
    (h_nodup : (walkVisits fuel start curr es).Nodup)
    (σ : SState) :
    ∀ s d, (s, d) ∈ walkEmits fuel start curr es →
      applySequentialL
        ((walkEmits fuel start curr es).map
          (fun e => (Register.given e.1, Register.given e.2))) σ
          (.given d) = σ (.given s) := by
  intro s d h_mem
  let regify : UInt32 × UInt32 → Register × Register :=
    fun e => (Register.given e.1, Register.given e.2)
  let sched := (walkEmits fuel start curr es).map regify
  have h_inj : Function.Injective (Register.given) := by
    intro a b h; injection h
  -- Membership in sched.
  have h_mem' : (Register.given s, Register.given d) ∈ sched :=
    List.mem_map.mpr ⟨(s, d), h_mem, rfl⟩
  -- Apply applySequentialL_at_dst_unique.
  apply applySequentialL_at_dst_unique sched σ _ _ h_mem'
  · -- Nodup of dsts.
    have h_map_eq : sched.map Prod.snd =
        ((walkEmits fuel start curr es).map Prod.snd).map Register.given := by
      show ((walkEmits fuel start curr es).map regify).map Prod.snd =
        ((walkEmits fuel start curr es).map Prod.snd).map Register.given
      rw [List.map_map, List.map_map]
      rfl
    rw [h_map_eq]
    -- Need: (xs.map Register.given).Nodup, from xs.Nodup + given injective.
    exact map_nodup_given _ (walkEmits_dsts_nodup fuel start curr es)
  · -- Source not earlier dst.
    intro pre post h_split cp' hcp' hcontra
    -- Use List.map_eq_append_iff to decompose.
    rw [List.map_eq_append_iff] at h_split
    obtain ⟨l₁, l₂_full, h_orig_split, h_l₁_eq, h_l₂_eq⟩ := h_split
    cases l₂_full with
    | nil => simp at h_l₂_eq
    | cons e l₂_rest =>
      simp at h_l₂_eq
      obtain ⟨h_e_eq, h_l₂_rest_eq⟩ := h_l₂_eq
      -- h_e_eq : (regify e) = (.given s, .given d). Extract s, d from e.
      have h_e_fst : e.1 = s := by
        have : (regify e).1 = (Register.given s, Register.given d).1 := by rw [h_e_eq]
        simp only [regify] at this
        injection this
      have h_e_snd : e.2 = d := by
        have : (regify e).2 = (Register.given s, Register.given d).2 := by rw [h_e_eq]
        simp only [regify] at this
        injection this
      have h_e_eq_pair : e = (s, d) := by
        obtain ⟨a, b⟩ := e
        simp at h_e_fst h_e_snd
        congr
      -- Now walkEmits = l₁ ++ (s, d) :: l₂_rest.
      rw [h_e_eq_pair] at h_orig_split
      -- cp' is in pre = l₁.map regify. So cp' = regify cp_orig for some cp_orig ∈ l₁.
      rw [← h_l₁_eq, List.mem_map] at hcp'
      obtain ⟨cp_orig, hcp_orig, hcp_eq⟩ := hcp'
      -- hcontra : cp'.2 = .given s. cp'.2 = (regify cp_orig).2 = .given cp_orig.2.
      have h_cp_orig_2 : cp_orig.2 = s := by
        have : (regify cp_orig).2 = cp'.2 := by rw [hcp_eq]
        simp only [regify] at this
        rw [hcontra] at this
        injection this
      -- Now apply walkEmits_non_clobbering.
      exact walkEmits_non_clobbering fuel start curr es h_nodup
        l₁ s d l₂_rest h_orig_split cp_orig hcp_orig h_cp_orig_2

/-! ## breakOneCycle correctness on a single cycle

Putting the pieces together: under `OnCycle start es`, the schedule that
`breakOneCycle` produces writes each cycle register's parallel-cycle
value into it. -/

/-- Applying `walkEmits.regify` on top of a state where `.temp` holds some
    value leaves `.temp` unchanged. -/
theorem applySequentialL_walkEmits_regify_preserves_temp
    (fuel : Nat) (start curr : UInt32) (es : Edges) (σ : SState) :
    applySequentialL
      ((walkEmits fuel start curr es).map
        (fun e => (Register.given e.1, Register.given e.2))) σ .temp =
      σ .temp := by
  apply applySequentialL_preserves_non_dst
  intro cp hcp
  rw [List.mem_map] at hcp
  obtain ⟨e, _, h_eq⟩ := hcp
  rw [← h_eq]
  simp

/-- For any register *not* in `walkEmits.dsts`, applying the regified
    schedule leaves it unchanged. -/
theorem applySequentialL_walkEmits_regify_preserves_non_dst_given
    (fuel : Nat) (start curr : UInt32) (es : Edges) (σ : SState)
    (r : UInt32) (h : r ∉ (walkEmits fuel start curr es).map Prod.snd) :
    applySequentialL
      ((walkEmits fuel start curr es).map
        (fun e => (Register.given e.1, Register.given e.2))) σ (.given r) =
      σ (.given r) := by
  apply applySequentialL_preserves_non_dst
  intro cp hcp
  rw [List.mem_map] at hcp
  obtain ⟨e, he, h_eq⟩ := hcp
  rw [← h_eq]
  intro hcontra
  simp only at hcontra
  apply h
  rw [List.mem_map]
  exact ⟨e, he, by injection hcontra⟩

/-! ## breakOneCycle correctness on one cycle -/

/-- Schedule produced by `breakOneCycle` with empty initial acc. -/
theorem breakOneCycle_schedule_eq
    (fuel : Nat) (start : UInt32) (es : Edges) :
    (breakOneCycle fuel .temp start es []).2 =
      [(.given start, Register.temp)] ++
      ((walkEmits fuel start start es).map
        (fun e => (Register.given e.1, Register.given e.2))) ++
      [(Register.temp, .given (walkCycle fuel start start es
          [(.given start, Register.temp)]).1)] := by
  unfold breakOneCycle
  simp [walkCycle_emits_eq]

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
