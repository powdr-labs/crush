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

/-! ## consPairs membership: each consecutive pair is in the result -/

/-- For `i < cycle.length - 1`, `(cycle[i+1], cycle[i])` is in `consPairs cycle`. -/
theorem consPairs_mem_pair
    (cycle : List UInt32) (i : Nat) (h : i + 1 < cycle.length) :
    (cycle.get ⟨i + 1, h⟩, cycle.get ⟨i, by omega⟩) ∈ consPairs cycle := by
  induction cycle generalizing i with
  | nil => simp at h
  | cons a rest ih =>
    cases rest with
    | nil => simp at h
    | cons b rest' =>
      simp only [consPairs]
      cases i with
      | zero =>
        simp [List.mem_cons]
      | succ k =>
        right
        have h' : k + 1 < (b :: rest').length := by
          simp at h ⊢
          omega
        exact ih k h'

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

/-- walkCycle's returned first component = walkVisits's last element
    (using `getLast!` to avoid dependent-type issues). -/
theorem walkCycle_fst_eq_walkVisits_getLast!
    (fuel : Nat) (start curr : UInt32) (es : Edges)
    (acc : List (Register × Register)) :
    (walkCycle fuel start curr es acc).1 =
      (walkVisits fuel start curr es).getLast! := by
  induction fuel generalizing curr es acc with
  | zero => simp [walkCycle, walkVisits]
  | succ n ih =>
    cases hsrc : srcOf? curr es with
    | none => simp [walkCycle, walkVisits, hsrc]
    | some source =>
      by_cases h : source = start
      · simp [walkCycle, walkVisits, hsrc, h]
      · have hwc : (walkCycle (n+1) start curr es acc).1 =
                   (walkCycle n start source (eraseDst curr es)
                     (acc ++ [(.given source, .given curr)])).1 := by
          simp [walkCycle, hsrc, h]
        have hwv : walkVisits (n+1) start curr es =
                   curr :: walkVisits n start source (eraseDst curr es) := by
          simp [walkVisits, hsrc, h]
        rw [hwc, ih, hwv]
        have h_ne_nil := walkVisits_ne_nil n start source (eraseDst curr es)
        cases h_vis : walkVisits n start source (eraseDst curr es) with
        | nil => exact absurd h_vis h_ne_nil
        | cons a rest => simp [List.getLast!]

/-! ## breakOneCycle correctness on a single cycle -/

/-- Helper: applying breakOneCycle's schedule, registers OTHER than the
    cycle's last (and not in walkEmits.dsts) are unchanged. -/
theorem breakOneCycle_preserves_non_cycle_dst
    (fuel : Nat) (start : UInt32) (es : Edges)
    (σ : SState) (r : UInt32)
    (h_ne_last : r ≠ (walkCycle fuel start start es
                       [(Register.given start, Register.temp)]).1)
    (h_not_dst : r ∉ (walkEmits fuel start start es).map Prod.snd) :
    applySequentialL (breakOneCycle fuel .temp start es []).2 σ
      (.given r) = σ (.given r) := by
  rw [breakOneCycle_schedule_eq]
  rw [applySequentialL_append, applySequentialL_append]
  simp only [applySequentialL_cons, applySequentialL_nil, applySequentialL_singleton]
  -- σ_3 = step σ_2 (.temp, .given last). For r ≠ last, σ_3(.given r) = σ_2(.given r).
  rw [step_other _ _ (fun h => h_ne_last (by injection h))]
  -- σ_2 = applySequentialL walkEmits.regify σ_1. For r ∉ walkEmits.dsts, σ_2(.given r) = σ_1(.given r).
  rw [applySequentialL_walkEmits_regify_preserves_non_dst_given _ _ _ _ _ _ h_not_dst]
  -- σ_1 = step σ (.given start, .temp). For r ≠ .temp constructor-wise, σ_1(.given r) = σ(.given r).
  simp [step]

/-- For the cycle's *last* register (the one walkCycle returns), the schedule
    writes σ(.given start) into it via the restore copy. -/
theorem breakOneCycle_writes_last
    (fuel : Nat) (start : UInt32) (es : Edges)
    (σ : SState) :
    applySequentialL (breakOneCycle fuel .temp start es []).2 σ
      (.given (walkCycle fuel start start es
                 [(Register.given start, Register.temp)]).1) =
      σ (.given start) := by
  rw [breakOneCycle_schedule_eq]
  rw [applySequentialL_append, applySequentialL_append]
  simp only [applySequentialL_cons, applySequentialL_nil, applySequentialL_singleton, step]
  -- After simp, the goal should be reduced. Let me check.
  rw [applySequentialL_walkEmits_regify_preserves_temp]
  simp [step]

/-- For a cycle dst that's *not* the last (i.e., (s, d) ∈ walkEmits),
    the schedule writes σ(.given s) into .given d. -/
theorem breakOneCycle_writes_non_last
    (fuel : Nat) (start : UInt32) (es : Edges)
    (h_nodup : (walkVisits fuel start start es).Nodup)
    (σ : SState) (s d : UInt32)
    (h_mem : (s, d) ∈ walkEmits fuel start start es)
    (h_ne_last : d ≠ (walkCycle fuel start start es
                       [(Register.given start, Register.temp)]).1) :
    applySequentialL (breakOneCycle fuel .temp start es []).2 σ
      (.given d) = σ (.given s) := by
  rw [breakOneCycle_schedule_eq]
  rw [applySequentialL_append, applySequentialL_append]
  simp only [applySequentialL_cons, applySequentialL_nil, applySequentialL_singleton]
  rw [step_other _ _ (fun h => h_ne_last (by injection h))]
  rw [walkEmits_regify_writes fuel start start es h_nodup _ s d h_mem]
  simp [step]

/-! ## breakOneCycle_sound — single cycle correctness

For each position `i` in the cycle, `breakOneCycle`'s schedule writes
the right value into `.given (cycle[i])`:

* `i < cycle.length - 1` → writes `σ(.given cycle[i+1])` (the next visit).
* `i = cycle.length - 1` → writes `σ(.given start)` (the cycle closure).
-/

/-- `getLast!` of a cons whose tail is non-empty equals `getLast!` of the tail. -/
private theorem getLast!_cons_cons
    {α : Type u} [Inhabited α] (a b : α) (rest : List α) :
    (a :: b :: rest).getLast! = (b :: rest).getLast! := by
  simp [List.getLast!]

/-- For a `Nodup` non-empty list, `get i` equals `getLast!` iff `i = length - 1`.
    Proven by induction on the list. -/
theorem nodup_get_eq_getLast!_iff :
    ∀ (xs : List UInt32) (_ : xs.Nodup) (_ : xs ≠ [])
      (i : Nat) (h_i : i < xs.length),
      xs.get ⟨i, h_i⟩ = xs.getLast! ↔ i = xs.length - 1
  | [],          _,         h_ne_nil, _,   _   => by simp at h_ne_nil
  | [a],         _,         _,        0,   _   => by simp [List.getLast!]
  | [_],         _,         _,        k+1, h_i => by simp at h_i
  | a :: b :: rest, h_nodup, _,        0,   _   => by
    rw [List.nodup_cons] at h_nodup
    obtain ⟨ha_notin, _⟩ := h_nodup
    rw [getLast!_cons_cons]
    show a = (b :: rest).getLast! ↔ 0 = (a :: b :: rest).length - 1
    constructor
    · intro h_eq
      have h_last_in : (b :: rest).getLast (by simp) ∈ b :: rest :=
        List.getLast_mem _
      have hL : (b :: rest).getLast! = (b :: rest).getLast (by simp) := by
        simp [List.getLast!, List.getLast_eq_getElem]
      rw [hL] at h_eq
      rw [← h_eq] at h_last_in
      exact absurd h_last_in ha_notin
    · intro h_eq
      simp at h_eq
  | a :: b :: rest, h_nodup, _,        k+1, h_i => by
    rw [List.nodup_cons] at h_nodup
    have h_rest_nodup : (b :: rest).Nodup := h_nodup.2
    have h_rest_ne_nil : (b :: rest) ≠ [] := by simp
    have h_k_lt : k < (b :: rest).length := by
      have : (a :: b :: rest).length = (b :: rest).length + 1 := by simp
      omega
    have ih := nodup_get_eq_getLast!_iff (b :: rest) h_rest_nodup h_rest_ne_nil k h_k_lt
    rw [getLast!_cons_cons]
    show (b :: rest).get ⟨k, h_k_lt⟩ = (b :: rest).getLast! ↔
         k + 1 = (a :: b :: rest).length - 1
    rw [ih]
    have : (a :: b :: rest).length = (b :: rest).length + 1 := by simp
    omega

/-- Combined breakOneCycle correctness for cycle registers. -/
theorem breakOneCycle_sound_at_cycle_idx
    (fuel : Nat) (start : UInt32) (es : Edges)
    (hC : OnCycle start es) (h_fuel : hC.choose.length ≤ fuel)
    (σ : SState) (i : Nat) (h_i : i < hC.choose.length) :
    applySequentialL (breakOneCycle fuel .temp start es []).2 σ
      (.given (hC.choose.get ⟨i, h_i⟩)) =
      σ (.given (if h : i + 1 < hC.choose.length
                  then hC.choose.get ⟨i + 1, h⟩
                  else start)) := by
  obtain ⟨h_ne_nil, h_head, h_nodup, h_path⟩ := hC.choose_spec
  have h_visits_eq : walkVisits fuel start start es = hC.choose :=
    walkVisits_eq_of_onCycle start es hC fuel h_fuel
  have h_nodup_visits : (walkVisits fuel start start es).Nodup := by
    rw [h_visits_eq]; exact h_nodup
  have h_last_eq :
      (walkCycle fuel start start es
        [(Register.given start, Register.temp)]).1 = hC.choose.getLast! := by
    rw [walkCycle_fst_eq_walkVisits_getLast!, h_visits_eq]
  by_cases h_last_pos : i + 1 < hC.choose.length
  · rw [dif_pos h_last_pos]
    have h_ne_last : hC.choose.get ⟨i, h_i⟩ ≠ hC.choose.getLast! := by
      intro hcontra
      rw [nodup_get_eq_getLast!_iff hC.choose h_nodup h_ne_nil i h_i] at hcontra
      omega
    have h_mem :
        (hC.choose.get ⟨i + 1, h_last_pos⟩, hC.choose.get ⟨i, h_i⟩) ∈
          walkEmits fuel start start es := by
      rw [walkEmits_eq_consPairs_walkVisits, h_visits_eq]
      exact consPairs_mem_pair hC.choose i h_last_pos
    exact breakOneCycle_writes_non_last fuel start es h_nodup_visits σ _ _ h_mem
      (h_last_eq ▸ h_ne_last)
  · rw [dif_neg h_last_pos]
    have h_i_eq : i = hC.choose.length - 1 := by omega
    have h_get_eq_last : hC.choose.get ⟨i, h_i⟩ = hC.choose.getLast! :=
      (nodup_get_eq_getLast!_iff hC.choose h_nodup h_ne_nil i h_i).mpr h_i_eq
    rw [h_get_eq_last, ← h_last_eq]
    exact breakOneCycle_writes_last fuel start es σ

/-! ## walkEmits ⊆ es -/

/-- Every pair emitted by `walkEmits` is an edge of the original `es`.
    walkCycle reads source via `srcOf?` on a (possibly eraseDst-shrunk)
    subset of `es`; both `srcOf?_mem` and `eraseDst_subset` push us back
    to `es`. -/
theorem walkEmits_subset_es
    (fuel : Nat) (start curr : UInt32) (es : Edges) :
    ∀ p ∈ walkEmits fuel start curr es, p ∈ es := by
  induction fuel generalizing curr es with
  | zero => simp [walkEmits]
  | succ n ih =>
    simp only [walkEmits]
    cases hsrc : srcOf? curr es with
    | none => simp
    | some source =>
      by_cases h_start : source = start
      · simp [h_start]
      · simp only [h_start, if_false]
        intro p hp
        rcases List.mem_cons.mp hp with heq | hmem
        · subst heq; exact srcOf?_mem es curr source hsrc
        · exact eraseDst_subset curr es _ (ih source (eraseDst curr es) p hmem)

/-! ## applyParallelLS reading lemmas -/

/-- When `(s, r) ∈ es` with `s ≠ r` and the graph has unique dsts,
    `applyParallelLS` at `.given r` returns `σ (.given s)`. -/
theorem applyParallelLS_at_writer
    (es : Edges) (σ : SState) (s r : UInt32)
    (hWF : UniqueDst es) (h_mem : (s, r) ∈ es) (h_ne : s ≠ r) :
    applyParallelLS es σ (.given r) = σ (.given s) := by
  show (match es.find? (Pair.appliesTo · r) with
        | some (src, _) => σ (.given src)
        | none          => σ (.given r)) = σ (.given s)
  rw [find?_dst_of_mem s r es hWF h_mem h_ne]

/-- When no non-self edge in `es` writes to `r`, `applyParallelLS` is identity. -/
theorem applyParallelLS_at_no_writer
    (es : Edges) (σ : SState) (r : UInt32)
    (h : ∀ e ∈ es, ¬ (e.2 = r ∧ e.1 ≠ e.2)) :
    applyParallelLS es σ (.given r) = σ (.given r) := by
  show (match es.find? (Pair.appliesTo · r) with
        | some (src, _) => σ (.given src)
        | none          => σ (.given r)) = σ (.given r)
  rw [find?_of_no_writer es r h]

/-! ## CyclePathTo encodes cycle edges -/

/-- The closing edge of a cycle: `(start, last_visit) ∈ es`. -/
theorem cyclePathTo_last_edge
    {start : UInt32} {es : Edges} {path : List UInt32}
    (h_path : CyclePathTo start es path) :
    (start, path.getLast!) ∈ es := by
  induction h_path with
  | last h_close =>
    rename_i es' curr_path
    have h_close' : (start, curr_path) ∈ es' := srcOf?_mem _ _ _ h_close
    show (start, [curr_path].getLast!) ∈ es'
    simp [List.getLast!]
    exact h_close'
  | step h_step h_ne_start _ ih =>
    rename_i es' curr_path next rest _
    have h_eq_last :
        (curr_path :: next :: rest).getLast! = (next :: rest).getLast! := by
      simp [List.getLast!]
    rw [h_eq_last]
    exact eraseDst_subset curr_path es' _ ih

/-! ## Nodup index injectivity -/

/-- For a `Nodup` list, `get` at distinct indices yields distinct elements. -/
private theorem nodup_get_inj :
    ∀ (xs : List UInt32) (_ : xs.Nodup) (i j : Nat)
      (hi : i < xs.length) (hj : j < xs.length),
      xs.get ⟨i, hi⟩ = xs.get ⟨j, hj⟩ → i = j
  | [],          _, _,   _,   hi, _,  _   => by simp at hi
  | _ :: _,      _, 0,   0,   _,  _,  _   => rfl
  | x :: rest,   h, 0,   j+1, _,  hj, heq => by
    rw [List.nodup_cons] at h
    have h_x_notin : x ∉ rest := h.1
    have hj' : j < rest.length := by simp at hj; omega
    have h_mem : rest.get ⟨j, hj'⟩ ∈ rest := List.get_mem rest ⟨j, hj'⟩
    have h_lhs : (x :: rest).get ⟨0, by simp⟩ = x := rfl
    have h_rhs : (x :: rest).get ⟨j+1, by simp at hj ⊢; omega⟩ =
                 rest.get ⟨j, hj'⟩ := rfl
    rw [h_lhs, h_rhs] at heq
    exact absurd (heq ▸ h_mem) h_x_notin
  | x :: rest,   h, i+1, 0,   hi, _,  heq => by
    rw [List.nodup_cons] at h
    have h_x_notin : x ∉ rest := h.1
    have hi' : i < rest.length := by simp at hi; omega
    have h_mem : rest.get ⟨i, hi'⟩ ∈ rest := List.get_mem rest ⟨i, hi'⟩
    have h_lhs : (x :: rest).get ⟨i+1, by simp at hi ⊢; omega⟩ =
                 rest.get ⟨i, hi'⟩ := rfl
    have h_rhs : (x :: rest).get ⟨0, by simp⟩ = x := rfl
    rw [h_lhs, h_rhs] at heq
    exact absurd (heq.symm ▸ h_mem) h_x_notin
  | x :: rest,   h, i+1, j+1, hi, hj, heq => by
    rw [List.nodup_cons] at h
    have h_rest_nodup : rest.Nodup := h.2
    have hi' : i < rest.length := by simp at hi; omega
    have hj' : j < rest.length := by simp at hj; omega
    have h_lhs : (x :: rest).get ⟨i+1, by simp at hi ⊢; omega⟩ =
                 rest.get ⟨i, hi'⟩ := rfl
    have h_rhs : (x :: rest).get ⟨j+1, by simp at hj ⊢; omega⟩ =
                 rest.get ⟨j, hj'⟩ := rfl
    have heq' : rest.get ⟨i, hi'⟩ = rest.get ⟨j, hj'⟩ := by
      rw [← h_lhs, ← h_rhs]; exact heq
    have ih := nodup_get_inj rest h_rest_nodup i j hi' hj' heq'
    omega

/-- Cycle elements at distinct indices are distinct. -/
private theorem cycle_elem_ne_of_idx_ne
    {xs : List UInt32} (h_nodup : xs.Nodup)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length)
    (h : i ≠ j) :
    xs.get ⟨i, hi⟩ ≠ xs.get ⟨j, hj⟩ :=
  fun heq => h (nodup_get_inj xs h_nodup i j hi hj heq)

/-! ## applyParallelLS at cycle positions -/

/-- For a cycle position `i < length - 1`, the parallel writer is `cycle[i+1]`. -/
theorem applyParallelLS_at_cycle_dst_non_last
    (start : UInt32) (es : Edges)
    (hWF : UniqueDst es)
    (hC : OnCycle start es)
    (fuel : Nat) (h_fuel : hC.choose.length ≤ fuel)
    (σ : SState)
    (i : Nat) (h_i_succ : i + 1 < hC.choose.length) :
    applyParallelLS es σ (.given (hC.choose.get ⟨i, by omega⟩)) =
      σ (.given (hC.choose.get ⟨i + 1, h_i_succ⟩)) := by
  obtain ⟨_, _, h_nodup, _⟩ := hC.choose_spec
  have h_visits_eq : walkVisits fuel start start es = hC.choose :=
    walkVisits_eq_of_onCycle start es hC fuel h_fuel
  have h_i : i < hC.choose.length := by omega
  have h_mem_emit :
      (hC.choose.get ⟨i + 1, h_i_succ⟩, hC.choose.get ⟨i, h_i⟩) ∈
        walkEmits fuel start start es := by
    rw [walkEmits_eq_consPairs_walkVisits, h_visits_eq]
    exact consPairs_mem_pair hC.choose i h_i_succ
  have h_mem : (hC.choose.get ⟨i + 1, h_i_succ⟩, hC.choose.get ⟨i, h_i⟩) ∈ es :=
    walkEmits_subset_es fuel start start es _ h_mem_emit
  have h_ne : hC.choose.get ⟨i + 1, h_i_succ⟩ ≠ hC.choose.get ⟨i, h_i⟩ :=
    cycle_elem_ne_of_idx_ne h_nodup h_i_succ h_i (by omega)
  exact applyParallelLS_at_writer es σ _ _ hWF h_mem h_ne

/-- For the last cycle position, the parallel writer is `start`. -/
theorem applyParallelLS_at_cycle_dst_last
    (start : UInt32) (es : Edges)
    (hWF : UniqueDst es)
    (h_no_self : ∀ e ∈ es, e.1 ≠ e.2)
    (hC : OnCycle start es)
    (σ : SState) :
    applyParallelLS es σ (.given hC.choose.getLast!) = σ (.given start) := by
  obtain ⟨h_ne_nil, h_head, h_nodup, h_path⟩ := hC.choose_spec
  have h_mem : (start, hC.choose.getLast!) ∈ es := cyclePathTo_last_edge h_path
  have h_ne : start ≠ hC.choose.getLast! := by
    cases h_len : hC.choose with
    | nil => exact absurd h_len h_ne_nil
    | cons a rest =>
      rw [h_len] at h_head
      simp at h_head
      rw [h_len] at h_nodup h_path
      subst h_head
      cases rest with
      | nil =>
        cases h_path with
        | last h_close =>
          have h_self : (a, a) ∈ es := srcOf?_mem _ _ _ h_close
          exact absurd (h_no_self _ h_self) (by simp)
      | cons b rest' =>
        rw [List.nodup_cons] at h_nodup
        have h_start_notin : a ∉ (b :: rest') := h_nodup.1
        have h_last_in : (b :: rest').getLast! ∈ (b :: rest') := by
          rw [show (b :: rest').getLast! = (b :: rest').getLast (by simp) from by
            simp [List.getLast!, List.getLast_eq_getElem]]
          exact List.getLast_mem _
        have h_last_eq : (a :: b :: rest').getLast! = (b :: rest').getLast! := by
          simp [List.getLast!]
        intro heq
        rw [h_last_eq] at heq
        rw [← heq] at h_last_in
        exact h_start_notin h_last_in
  exact applyParallelLS_at_writer es σ _ _ hWF h_mem h_ne

/-! ## breakOneCycle realises one cycle's parallel effect -/

/-- The unified breakOneCycle correctness: at every cycle node, the schedule
    writes `applyParallelLS es σ` for that node. -/
theorem breakOneCycle_sound_at_cycle
    (start : UInt32) (es : Edges)
    (hWF : UniqueDst es)
    (h_no_self : ∀ e ∈ es, e.1 ≠ e.2)
    (hC : OnCycle start es)
    (fuel : Nat) (h_fuel : hC.choose.length ≤ fuel)
    (σ : SState)
    (i : Nat) (h_i : i < hC.choose.length) :
    applySequentialL (breakOneCycle fuel .temp start es []).2 σ
      (.given (hC.choose.get ⟨i, h_i⟩)) =
      applyParallelLS es σ (.given (hC.choose.get ⟨i, h_i⟩)) := by
  by_cases h_last_pos : i + 1 < hC.choose.length
  · -- non-last: cycle[i+1] is the writer
    rw [breakOneCycle_sound_at_cycle_idx fuel start es hC h_fuel σ i h_i]
    rw [dif_pos h_last_pos]
    rw [applyParallelLS_at_cycle_dst_non_last start es hWF hC fuel h_fuel σ i h_last_pos]
  · -- last: start is the writer
    rw [breakOneCycle_sound_at_cycle_idx fuel start es hC h_fuel σ i h_i]
    rw [dif_neg h_last_pos]
    obtain ⟨_, _, h_nodup, _⟩ := hC.choose_spec
    have h_ne_nil : hC.choose ≠ [] := hC.choose_spec.1
    have h_i_eq : i = hC.choose.length - 1 := by omega
    have h_get_eq_last : hC.choose.get ⟨i, h_i⟩ = hC.choose.getLast! :=
      (nodup_get_eq_getLast!_iff hC.choose h_nodup h_ne_nil i h_i).mpr h_i_eq
    rw [h_get_eq_last]
    rw [applyParallelLS_at_cycle_dst_last start es hWF h_no_self hC σ]

/-! ## smallestDst lemmas -/

/-- Once the fold's accumulator becomes `some _`, it stays `some _`. -/
private theorem smallestDst_fold_some_persists
    (acc : UInt32) (es : Edges) :
    ∃ x, es.foldl (init := some acc)
            (fun best e => some <| best.elim e.2
              (Nat.min e.2.toNat ·.toNat |>.toUInt32)) = some x := by
  induction es generalizing acc with
  | nil => exact ⟨acc, by simp⟩
  | cons e rest ih =>
    simp only [List.foldl_cons]
    exact ih _

/-- `smallestDst` returns `none` exactly when the list is empty. -/
theorem smallestDst_eq_none_iff (es : Edges) :
    smallestDst es = none ↔ es = [] := by
  constructor
  · intro h
    cases es with
    | nil => rfl
    | cons e rest =>
      simp only [smallestDst, List.foldl_cons, Option.elim_none] at h
      obtain ⟨x, hx⟩ := smallestDst_fold_some_persists e.2 rest
      rw [hx] at h
      exact absurd h (by simp)
  · intro h; subst h; rfl

/-- Auxiliary: `(Nat.min n m).toUInt32 ∈ {n.toUInt32, m.toUInt32}` for any `n, m`. -/
private theorem nat_min_toUInt32_eq_or
    (n m : Nat) :
    (Nat.min n m).toUInt32 = n.toUInt32 ∨ (Nat.min n m).toUInt32 = m.toUInt32 := by
  by_cases h : n ≤ m
  · left
    have : Nat.min n m = n := Nat.min_eq_left h
    rw [this]
  · right
    have h' : m ≤ n := Nat.le_of_lt (Nat.lt_of_not_le h)
    have : Nat.min n m = m := Nat.min_eq_right h'
    rw [this]

/-- The fold accumulator value is in `acc ∪ dsts es` when non-empty. -/
private theorem smallestDst_fold_mem
    (acc : UInt32) (es : Edges) :
    ∀ x, es.foldl (init := some acc)
            (fun best e => some <| best.elim e.2
              (Nat.min e.2.toNat ·.toNat |>.toUInt32)) = some x →
         x = acc ∨ x ∈ es.map Prod.snd := by
  induction es generalizing acc with
  | nil =>
    intro x hx; simp at hx; left; exact hx.symm
  | cons e rest ih =>
    intro x hx
    simp only [List.foldl_cons, Option.elim_some] at hx
    have ih' := ih _ x hx
    rcases ih' with h_eq | h_mem
    · -- new acc = (Nat.min e.2.toNat acc.toNat).toUInt32, equal to e.2 or acc
      have hor := nat_min_toUInt32_eq_or e.2.toNat acc.toNat
      have h_e2 : e.2.toNat.toUInt32 = e.2 := UInt32.ofNat_toNat
      have h_acc : acc.toNat.toUInt32 = acc := UInt32.ofNat_toNat
      rw [h_e2, h_acc] at hor
      rcases hor with h_e | h_acc'
      · right
        have hx : x = e.2 := h_eq.trans h_e
        rw [hx, List.map_cons]
        exact List.mem_cons_self
      · left
        exact h_eq.trans h_acc'
    · right
      rw [List.map_cons]
      exact List.mem_cons_of_mem _ h_mem

/-- If `smallestDst es = some d`, then `d` is a dst in `es`. -/
theorem smallestDst_some_mem
    (es : Edges) (d : UInt32) (h : smallestDst es = some d) :
    d ∈ es.map Prod.snd := by
  cases es with
  | nil => simp [smallestDst] at h
  | cons e rest =>
    simp only [smallestDst, List.foldl_cons, Option.elim_none] at h
    have := smallestDst_fold_mem e.2 rest d h
    rcases this with h_eq | h_mem
    · subst h_eq
      rw [List.map_cons]
      exact List.mem_cons_self
    · rw [List.map_cons]
      exact List.mem_cons_of_mem _ h_mem

/-! ## applyParallelLS interactions -/

/-- `eraseDst` on a `UniqueDst` graph: at any `r ≠ d`, the parallel effect
    is unchanged. -/
theorem applyParallelLS_eraseDst_ne
    (d : UInt32) (es : Edges) (hWF : UniqueDst es)
    (σ : SState) (r : UInt32) (h_ne : r ≠ d) :
    applyParallelLS (eraseDst d es) σ (.given r) = applyParallelLS es σ (.given r) := by
  by_cases h_writer : ∃ s, (s, r) ∈ es ∧ s ≠ r
  · obtain ⟨s, h_mem, h_ne_s⟩ := h_writer
    have h_mem' : (s, r) ∈ eraseDst d es := by
      rw [mem_eraseDst]; exact ⟨h_mem, h_ne⟩
    have hWF' : UniqueDst (eraseDst d es) := eraseDst_uniqueDst d es hWF
    rw [applyParallelLS_at_writer (eraseDst d es) σ s r hWF' h_mem' h_ne_s]
    rw [applyParallelLS_at_writer es σ s r hWF h_mem h_ne_s]
  · have h_es : ∀ e ∈ es, ¬ (e.2 = r ∧ e.1 ≠ e.2) := by
      intro e he ⟨h_eq, h_ne_e⟩
      obtain ⟨s, t⟩ := e
      simp at h_eq
      subst h_eq
      exact h_writer ⟨s, he, h_ne_e⟩
    have h_es' : ∀ e ∈ eraseDst d es, ¬ (e.2 = r ∧ e.1 ≠ e.2) :=
      fun e he => h_es e (eraseDst_subset _ _ _ he)
    rw [applyParallelLS_at_no_writer (eraseDst d es) σ r h_es']
    rw [applyParallelLS_at_no_writer es σ r h_es]

/-! ## walkCycle residual = filter not-in-erased dsts -/

/-- The dsts that walkCycle actually erases (i.e., excluding the "premature
    termination" cases). When the walk closes properly, this equals
    `walkVisits`. -/
def walkErased (fuel : Nat) (start curr : UInt32) (es : Edges) : List UInt32 :=
  match fuel with
  | 0 => []
  | n+1 =>
    match srcOf? curr es with
    | none => []
    | some source =>
      if source = start then [curr]
      else curr :: walkErased n start source (eraseDst curr es)

/-- The edges remaining after `walkCycle` are exactly those whose destination
    is not in the actually-erased set. -/
theorem walkCycle_residual_eq
    (fuel : Nat) (start curr : UInt32) (es : Edges)
    (acc : List (Register × Register)) :
    (walkCycle fuel start curr es acc).2.1 =
      es.filter (fun e => decide (e.2 ∉ walkErased fuel start curr es)) := by
  induction fuel generalizing curr es acc with
  | zero =>
    simp only [walkCycle, walkErased]
    rw [List.filter_eq_self.mpr]
    intro a _; simp
  | succ n ih =>
    cases hsrc : srcOf? curr es with
    | none =>
      simp only [walkCycle, walkErased, hsrc]
      rw [List.filter_eq_self.mpr]
      intro a _; simp
    | some source =>
      by_cases h_start : source = start
      · simp only [walkCycle, walkErased, hsrc, h_start, if_true]
        show eraseDst curr es =
          es.filter (fun e => decide (e.2 ∉ [curr]))
        unfold eraseDst
        apply List.filter_congr
        intro e _
        simp only [List.mem_singleton]
        by_cases h : e.2 = curr
        · simp [h]
        · simp [h]
      · simp only [walkCycle, walkErased, hsrc, h_start, if_false]
        rw [ih]
        show (eraseDst curr es).filter
              (fun e => decide (e.2 ∉ walkErased n start source (eraseDst curr es))) =
             es.filter (fun e => decide
              (e.2 ∉ curr :: walkErased n start source (eraseDst curr es)))
        rw [show eraseDst curr es =
            es.filter (fun e => decide (e.2 ≠ curr)) from by
          unfold eraseDst
          apply List.filter_congr
          intro e _
          by_cases h : e.2 = curr
          · simp [h]
          · simp [h]]
        rw [List.filter_filter]
        apply List.filter_congr
        intro e _
        by_cases h1 : e.2 = curr
        · simp [h1]
        · by_cases h2 : e.2 ∈ walkErased n start source (eraseDst curr es)
          · simp [h1, h2]
          · simp [h1, h2, List.mem_cons]

/-- Under `CyclePathTo`, `walkErased` returns the same path as walkVisits.
    The proof is by induction on the cyclepath. -/
theorem walkErased_eq_of_cyclePathTo
    {path : List UInt32} {start : UInt32} {es : Edges}
    (hpath : CyclePathTo start es path)
    {fuel : Nat} (h_fuel : path.length ≤ fuel)
    {curr : UInt32} (h_head : path.head? = some curr) :
    walkErased fuel start curr es = path := by
  induction hpath generalizing fuel curr with
  | last h_close =>
    rename_i es' curr_path
    simp at h_head
    subst h_head
    cases fuel with
    | zero => simp at h_fuel
    | succ n =>
      simp only [walkErased]
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
      simp only [walkErased]
      rw [h_step]
      simp [h_ne_start]
      exact ih h_fuel' rfl

/-- Under `OnCycle`, `walkErased` returns the cycle's path. -/
theorem walkErased_eq_of_onCycle
    (start : UInt32) (es : Edges)
    (hC : OnCycle start es)
    (fuel : Nat) (h_fuel : hC.choose.length ≤ fuel) :
    walkErased fuel start start es = hC.choose := by
  obtain ⟨_, h_head, _, h_path⟩ := hC.choose_spec
  exact walkErased_eq_of_cyclePathTo h_path h_fuel h_head

/-! ## Cycle nodes characterization -/

/-- The cycle starting at `start` (when `OnCycle start es` holds). -/
noncomputable def cycleOf (start : UInt32) (es : Edges) (hC : OnCycle start es) :
    List UInt32 := hC.choose

/-- The residual after breakOneCycle is `es` minus edges whose dsts are in the
    cycle starting at `start`. -/
theorem breakOneCycle_residual
    (start : UInt32) (es : Edges) (hC : OnCycle start es)
    (fuel : Nat) (h_fuel : (cycleOf start es hC).length ≤ fuel)
    (acc : List (Register × Register)) :
    (breakOneCycle fuel .temp start es acc).1 =
      es.filter (fun e => decide (e.2 ∉ cycleOf start es hC)) := by
  unfold breakOneCycle
  simp only
  rw [walkCycle_residual_eq]
  rw [walkErased_eq_of_onCycle start es hC fuel h_fuel]
  rfl

/-! ## Cycle disjointness via UniqueDst

If two cycles share any node, they're the same cycle. We use this to show
that the residual still satisfies AllOnCycle. -/

/-- Following `srcOf?` from `curr` for `n` steps (returning the visited
    sequence in reverse-walk order). Used to phrase deterministic chains. -/
private def writerChain (n : Nat) (curr : UInt32) (es : Edges) : List UInt32 :=
  match n with
  | 0     => [curr]
  | n + 1 => match srcOf? curr es with
            | none      => [curr]
            | some next => curr :: writerChain n next es

/-! ## Phase 2 ready property and its preservation -/

/-- A list of edges where every destination is on a (forward) cycle. -/
def AllOnCycle (es : Edges) : Prop :=
  ∀ d, d ∈ es.map Prod.snd → OnCycle d es

/-- Helper: if `(s, r) ∈ es` and `r ∈ es.map Prod.snd`, this is the same
    membership statement (mapping respects). -/
private theorem mem_dsts_of_edge_mem
    {es : Edges} {s r : UInt32} (h : (s, r) ∈ es) :
    r ∈ es.map Prod.snd := by
  rw [List.mem_map]
  exact ⟨(s, r), h, rfl⟩

/-! ## Cycle uniqueness via writer chain determinism

The writer chain `srcOf?` is deterministic, so cycles sharing any node must
be the same cycle (as sets). We use this to prove that the residual after
breakOneCycle still satisfies `AllOnCycle`. -/

/-- `srcOf?` is the unique writer (under `UniqueDst`). -/
theorem srcOf?_eq_some_of_mem
    (es : Edges) (s r : UInt32) (hWF : UniqueDst es) (h_mem : (s, r) ∈ es) :
    srcOf? r es = some s := by
  unfold srcOf?
  have h_find : es.find? (fun e => e.2 = r) = some (s, r) := by
    induction es with
    | nil => simp at h_mem
    | cons e rest ih =>
      have hWF' : UniqueDst rest := UniqueDst_cons hWF
      rcases List.mem_cons.mp h_mem with heq | hmem'
      · subst heq; simp [List.find?_cons]
      · obtain ⟨a, b⟩ := e
        by_cases h_e_r : b = r
        · -- (a, b) and (s, r) both have dst b = r. By UniqueDst, a = s.
          subst h_e_r
          have hh := hWF a s b List.mem_cons_self (List.mem_cons_of_mem _ hmem')
          subst hh
          simp [List.find?_cons]
        · simp only [List.find?_cons, h_e_r, ↓reduceIte]
          exact ih hWF' hmem'
  rw [h_find]; rfl

/-- The writer of any `cycleOf` node is also in `cycleOf` (under UniqueDst). -/
theorem cycleOf_closed_under_writer
    (start : UInt32) (es : Edges) (hC : OnCycle start es)
    (hWF : UniqueDst es)
    (v : UInt32) (h_v : v ∈ cycleOf start es hC) :
    ∃ u, srcOf? v es = some u ∧ u ∈ cycleOf start es hC := by
  unfold cycleOf at h_v ⊢
  obtain ⟨_, h_head, _, h_path⟩ := hC.choose_spec
  -- v is at some index i in cycleOf. The writer is the (i+1)-th element
  -- if i < length-1, else `start`.
  obtain ⟨n, h_get⟩ := List.mem_iff_get.mp h_v
  let i := n.val
  have hi : i < hC.choose.length := n.isLt
  have h_get' : hC.choose.get ⟨i, hi⟩ = v := h_get
  by_cases h_last : i + 1 < hC.choose.length
  · -- non-last: writer is cycleOf[i+1]
    have h_walk_eq : walkVisits hC.choose.length start start es = hC.choose :=
      walkVisits_eq_of_onCycle start es hC hC.choose.length (Nat.le_refl _)
    have h_mem_emit :
        (hC.choose.get ⟨i + 1, h_last⟩, hC.choose.get ⟨i, hi⟩) ∈
          walkEmits hC.choose.length start start es := by
      rw [walkEmits_eq_consPairs_walkVisits, h_walk_eq]
      exact consPairs_mem_pair hC.choose i h_last
    have h_in_es : (hC.choose.get ⟨i + 1, h_last⟩, hC.choose.get ⟨i, hi⟩) ∈ es :=
      walkEmits_subset_es _ _ _ _ _ h_mem_emit
    rw [h_get'] at h_in_es
    refine ⟨hC.choose.get ⟨i + 1, h_last⟩, ?_, List.get_mem _ _⟩
    exact srcOf?_eq_some_of_mem es _ _ hWF h_in_es
  · -- last position: writer is start
    have h_i_eq : i = hC.choose.length - 1 := by
      have : i < hC.choose.length := hi
      omega
    have h_ne_nil : hC.choose ≠ [] := hC.choose_spec.1
    obtain ⟨_, _, h_nodup, _⟩ := hC.choose_spec
    have h_get_eq_last : hC.choose.get ⟨i, hi⟩ = hC.choose.getLast! :=
      (nodup_get_eq_getLast!_iff hC.choose h_nodup h_ne_nil i hi).mpr h_i_eq
    have h_last_in_es : (start, hC.choose.getLast!) ∈ es :=
      cyclePathTo_last_edge h_path
    rw [← h_get', h_get_eq_last]
    refine ⟨start, srcOf?_eq_some_of_mem es _ _ hWF h_last_in_es, ?_⟩
    -- start is in cycleOf (it's the head)
    cases h_choose : hC.choose with
    | nil => exact absurd h_choose h_ne_nil
    | cons a rest =>
      rw [h_choose] at h_head
      simp at h_head
      subst h_head
      exact List.mem_cons_self

/-! ## Iterated writer chain -/

/-- `n` applications of `srcOf?` starting at `v`. `none` if the chain breaks. -/
def iterWriter (n : Nat) (v : UInt32) (es : Edges) : Option UInt32 :=
  match n with
  | 0     => some v
  | k + 1 => (iterWriter k v es).bind (fun u => srcOf? u es)

@[simp] theorem iterWriter_zero (v : UInt32) (es : Edges) :
    iterWriter 0 v es = some v := rfl

theorem iterWriter_succ (n : Nat) (v : UInt32) (es : Edges) :
    iterWriter (n + 1) v es = (iterWriter n v es).bind (fun u => srcOf? u es) :=
  rfl

/-- The writer chain from a `cycleOf` node stays in `cycleOf` after any
    number of iterations (under `UniqueDst`). -/
theorem cycleOf_closed_under_iterWriter
    (start : UInt32) (es : Edges) (hC : OnCycle start es)
    (hWF : UniqueDst es)
    (n : Nat) (v : UInt32) (h_v : v ∈ cycleOf start es hC) :
    ∃ u, iterWriter n v es = some u ∧ u ∈ cycleOf start es hC := by
  induction n with
  | zero => exact ⟨v, rfl, h_v⟩
  | succ k ih =>
    obtain ⟨u, h_iter, h_u⟩ := ih
    obtain ⟨w, h_src, h_w⟩ := cycleOf_closed_under_writer start es hC hWF u h_u
    refine ⟨w, ?_, h_w⟩
    rw [iterWriter_succ, h_iter]
    simp [h_src]

/-! ## Cycle path's writer chain matches the path -/

/-- The writer of `path.get ⟨i, _⟩` in `es` is `path.get ⟨i+1, _⟩`. -/
theorem cyclePathTo_writer_step
    {start : UInt32} {es : Edges} {path : List UInt32}
    (h_path : CyclePathTo start es path)
    (hWF : UniqueDst es)
    (h_head : path.head? = some start)
    (h_nodup : path.Nodup)
    (i : Nat) (h_i_succ : i + 1 < path.length) :
    srcOf? (path.get ⟨i, by omega⟩) es = some (path.get ⟨i + 1, h_i_succ⟩) := by
  -- Under OnCycle: walkEmits = consPairs path ⊆ es.
  have hC : OnCycle start es := ⟨path, by
    constructor
    · intro h_eq; rw [h_eq] at h_head; simp at h_head
    refine ⟨h_head, h_nodup, h_path⟩⟩
  -- We use the same machinery as cycleOf_closed_under_writer, since path
  -- can be picked from hC. The cleanest way: replicate the argument.
  have h_walk_eq : walkVisits path.length start start es = path := by
    apply walkVisits_eq_of_cyclePathTo h_path (Nat.le_refl _) h_head
  have h_mem_emit :
      (path.get ⟨i + 1, h_i_succ⟩, path.get ⟨i, by omega⟩) ∈
        walkEmits path.length start start es := by
    rw [walkEmits_eq_consPairs_walkVisits, h_walk_eq]
    exact consPairs_mem_pair path i h_i_succ
  have h_in_es : (path.get ⟨i + 1, h_i_succ⟩, path.get ⟨i, by omega⟩) ∈ es :=
    walkEmits_subset_es _ _ _ _ _ h_mem_emit
  exact srcOf?_eq_some_of_mem es _ _ hWF h_in_es

/-- The writer of `path.getLast!` in `es` is `start`. -/
theorem cyclePathTo_writer_close
    {start : UInt32} {es : Edges} {path : List UInt32}
    (h_path : CyclePathTo start es path)
    (hWF : UniqueDst es)
    (h_ne_nil : path ≠ []) :
    srcOf? path.getLast! es = some start := by
  have h_in_es : (start, path.getLast!) ∈ es := cyclePathTo_last_edge h_path
  exact srcOf?_eq_some_of_mem es _ _ hWF h_in_es

/-- Under `CyclePathTo`, walking `i` writer steps from the head lands on `path[i]`. -/
theorem iterWriter_path_step
    {start : UInt32} {es : Edges} {path : List UInt32}
    (h_path : CyclePathTo start es path)
    (hWF : UniqueDst es)
    (h_head : path.head? = some start)
    (h_nodup : path.Nodup)
    (i : Nat) (h_i : i < path.length) :
    iterWriter i start es = some (path.get ⟨i, h_i⟩) := by
  induction i with
  | zero =>
    show some start = some (path.get ⟨0, h_i⟩)
    -- path is non-empty since 0 < path.length
    match path, h_head with
    | [], h => simp at h
    | a :: rest, h =>
      simp at h
      subst h
      rfl
  | succ k ih =>
    have h_k : k < path.length := by omega
    have h_k_lt : k + 1 < path.length := h_i
    have ih' := ih h_k
    rw [iterWriter_succ, ih']
    show (some (path.get ⟨k, h_k⟩)).bind (fun u => srcOf? u es) =
         some (path.get ⟨k + 1, h_k_lt⟩)
    simp only [Option.bind_some]
    exact cyclePathTo_writer_step h_path hWF h_head h_nodup k h_k_lt

/-- Walking `path.length` writer steps from the head lands back on the head
    (since the cycle closes). -/
theorem iterWriter_path_close
    {start : UInt32} {es : Edges} {path : List UInt32}
    (h_path : CyclePathTo start es path)
    (hWF : UniqueDst es)
    (h_head : path.head? = some start)
    (h_nodup : path.Nodup)
    (h_ne_nil : path ≠ []) :
    iterWriter path.length start es = some start := by
  have h_len_pos : 0 < path.length := List.length_pos_iff.mpr h_ne_nil
  have h_last : path.length - 1 < path.length := by omega
  have ih := iterWriter_path_step h_path hWF h_head h_nodup (path.length - 1) h_last
  rw [show path.length = (path.length - 1) + 1 from by omega]
  rw [iterWriter_succ, ih]
  show (some (path.get ⟨path.length - 1, h_last⟩)).bind (fun u => srcOf? u es) =
       some start
  simp only [Option.bind_some]
  have h_getLast : path.get ⟨path.length - 1, h_last⟩ = path.getLast! := by
    match path, h_ne_nil with
    | [], h => exact absurd rfl h
    | a :: rest, _ => simp [List.getLast!, List.getLast_eq_getElem]
  rw [h_getLast]
  exact cyclePathTo_writer_close h_path hWF h_ne_nil

/-! ## Cycle disjointness -/

/-- If `r ∉ cycleOf` and `r` is on a cycle in `es`, then `r`'s cycle is
    disjoint from `cycleOf`. -/
theorem cycle_disjoint_of_start_not_in
    (start : UInt32) (es : Edges) (hC : OnCycle start es)
    (hWF : UniqueDst es)
    (r : UInt32) (hR : OnCycle r es) (h_disjoint : r ∉ cycleOf start es hC) :
    ∀ v, v ∈ cycleOf r es hR → v ∉ cycleOf start es hC := by
  intro v h_v_in_R h_v_in_start
  obtain ⟨_, h_head_R, h_nodup_R, h_path_R⟩ := hR.choose_spec
  -- v ∈ cycleOf r es hR means v ∈ hR.choose. Position is some i_v.
  obtain ⟨n_v, h_get_v⟩ := List.mem_iff_get.mp h_v_in_R
  let i_v := n_v.val
  have h_i_v : i_v < hR.choose.length := n_v.isLt
  -- Walking (length - i_v) writer steps from r in es lands at v.
  -- Then walking more steps stays in cycleOf (since v ∈ cycleOf).
  -- After length total steps from r, we're back at r, so r ∈ cycleOf.
  have h_ne_nil_R : hR.choose ≠ [] := hR.choose_spec.1
  -- iterWriter (length) r es = some r.
  have h_close : iterWriter hR.choose.length r es = some r :=
    iterWriter_path_close h_path_R hWF h_head_R h_nodup_R h_ne_nil_R
  -- v ∈ cycleOf start es hC.
  have h_v_eq : hR.choose.get ⟨i_v, h_i_v⟩ = v := h_get_v
  -- From any step k where iterWriter k r es = some w with w ∈ cycleOf,
  -- iterWriter (k + j) r es = some w' with w' ∈ cycleOf (for any j).
  -- We use this at k where iterWriter k r es = some v (some step k ≤ length).
  -- The step k = length - i_v.
  -- Let me prove this directly.
  -- iterWriter k r es for various k:
  --   k = 0: some r (= path_R.head)
  --   k = i: some path_R[i]
  -- At k = i_v: iterWriter i_v r es = some path_R[i_v] = some v.
  have h_at_v : iterWriter i_v r es = some v := by
    rw [← h_v_eq]
    exact iterWriter_path_step h_path_R hWF h_head_R h_nodup_R i_v h_i_v
  -- Now from v ∈ cycleOf start es hC, iterWriter k v es stays in cycleOf.
  -- We want iterWriter (length - i_v) v es to land at r (the closing of R's cycle).
  -- That requires showing the rotation property.
  -- Alternative: prove "iterWriter (i_v + j) r es = (iterWriter j v es)" via iterWriter composition.
  have h_compose : ∀ j, iterWriter (i_v + j) r es =
                  (iterWriter j v es) := by
    intro j
    induction j with
    | zero => simp; exact h_at_v
    | succ m ih_j =>
      rw [show i_v + (m + 1) = (i_v + m) + 1 from by omega]
      rw [iterWriter_succ, iterWriter_succ, ih_j]
  -- After length - i_v more steps from v, we're at iterWriter length r es = some r.
  have h_steps : i_v + (hR.choose.length - i_v) = hR.choose.length := by omega
  have h_combined : iterWriter (hR.choose.length - i_v) v es = some r := by
    rw [← h_compose, h_steps]; exact h_close
  -- But v ∈ cycleOf start es hC: walking from v stays in cycleOf.
  obtain ⟨u, h_iter_u, h_u_in⟩ :=
    cycleOf_closed_under_iterWriter start es hC hWF (hR.choose.length - i_v) v h_v_in_start
  rw [h_iter_u] at h_combined
  -- h_combined : some u = some r → u = r. So r ∈ cycleOf.
  injection h_combined with h_u_eq_r
  rw [← h_u_eq_r] at h_disjoint
  exact h_disjoint h_u_in

/-! ## CyclePathTo lifts to subsets disjoint from path -/

/-- `srcOf?` is unchanged by filtering, for nodes outside the removed set. -/
theorem srcOf?_filter_ne_removed
    (es : Edges) (removed : List UInt32) (v : UInt32) (h_v : v ∉ removed) :
    srcOf? v (es.filter (fun e => decide (e.2 ∉ removed))) = srcOf? v es := by
  unfold srcOf?
  congr 1
  induction es with
  | nil => simp
  | cons e rest ih =>
    by_cases h_keep : e.2 ∈ removed
    · -- e is filtered out
      have h_e_ne_v : e.2 ≠ v := by intro heq; rw [heq] at h_keep; exact h_v h_keep
      have h_keep_dec : decide (e.2 ∉ removed) = false := by simp [h_keep]
      rw [List.filter_cons, h_keep_dec]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [List.find?_cons]
      have : decide (e.2 = v) = false := by simp [h_e_ne_v]
      rw [this]
      exact ih
    · -- e is kept by the filter
      have h_keep_dec : decide (e.2 ∉ removed) = true := by simp [h_keep]
      rw [List.filter_cons, h_keep_dec]
      simp only [↓reduceIte]
      rw [List.find?_cons, List.find?_cons]
      by_cases h_e_v : e.2 = v
      · have : decide (e.2 = v) = true := by simp [h_e_v]
        rw [this]
      · have : decide (e.2 = v) = false := by simp [h_e_v]
        rw [this]
        exact ih

/-- `eraseDst d (filter es) = filter (eraseDst d es)`. -/
theorem eraseDst_filter_swap
    (es : Edges) (removed : List UInt32) (d : UInt32) :
    eraseDst d (es.filter (fun e => decide (e.2 ∉ removed))) =
      (eraseDst d es).filter (fun e => decide (e.2 ∉ removed)) := by
  unfold eraseDst
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro e _
  -- (decide ¬e.2 ∈ removed) && (e.2 != d) = (e.2 != d) && (decide ¬e.2 ∈ removed)
  exact Bool.and_comm _ _

/-- A `CyclePathTo` lifts to any filter that doesn't remove its dsts. -/
theorem cyclePathTo_lift_disjoint
    {start : UInt32} {es : Edges} {path : List UInt32}
    (h_path : CyclePathTo start es path)
    (removed : List UInt32)
    (h_disjoint : ∀ v ∈ path, v ∉ removed) :
    CyclePathTo start (es.filter (fun e => decide (e.2 ∉ removed))) path := by
  induction h_path with
  | last h_close =>
    rename_i es_inner curr_path
    apply CyclePathTo.last
    rw [srcOf?_filter_ne_removed]
    · exact h_close
    · exact h_disjoint curr_path (by simp)
  | step h_step h_ne_start _ ih =>
    rename_i es_inner curr_path next rest _
    apply CyclePathTo.step
    · rw [srcOf?_filter_ne_removed]
      · exact h_step
      · exact h_disjoint curr_path (by simp)
    · exact h_ne_start
    · rw [eraseDst_filter_swap]
      apply ih
      intro v hv
      apply h_disjoint
      simp [hv]

/-! ## AllOnCycle preservation under breakOneCycle's residual -/

/-- After breakOneCycle removes a cycle, the residual still has all dsts on
    cycles (in the residual). -/
theorem allOnCycle_preserved_by_breakOneCycle
    (start : UInt32) (es : Edges) (hC : OnCycle start es)
    (hWF : UniqueDst es)
    (h_all : AllOnCycle es)
    (fuel : Nat) (h_fuel : (cycleOf start es hC).length ≤ fuel)
    (acc : List (Register × Register)) :
    AllOnCycle (breakOneCycle fuel .temp start es acc).1 := by
  rw [breakOneCycle_residual start es hC fuel h_fuel acc]
  intro d h_d
  -- d ∈ filter.map Prod.snd
  rw [List.mem_map] at h_d
  obtain ⟨e, h_e_mem, h_e_eq⟩ := h_d
  rw [List.mem_filter] at h_e_mem
  obtain ⟨h_in_es, h_dst_notin⟩ := h_e_mem
  simp at h_dst_notin
  -- d = e.2, d ∉ cycleOf
  have h_d_in_es : d ∈ es.map Prod.snd := by
    rw [List.mem_map]
    exact ⟨e, h_in_es, h_e_eq⟩
  have h_d_notin_cycle : d ∉ cycleOf start es hC := h_e_eq ▸ h_dst_notin
  -- By AllOnCycle es, OnCycle d es with some path P_d.
  have hD : OnCycle d es := h_all d h_d_in_es
  obtain ⟨_, h_head_D, h_nodup_D, h_path_D⟩ := hD.choose_spec
  have h_disjoint : ∀ v, v ∈ cycleOf d es hD → v ∉ cycleOf start es hC :=
    cycle_disjoint_of_start_not_in start es hC hWF d hD h_d_notin_cycle
  -- Lift CyclePathTo from es to es.filter.
  have h_path_lifted : CyclePathTo d (es.filter
      (fun e => decide (e.2 ∉ cycleOf start es hC))) hD.choose := by
    apply cyclePathTo_lift_disjoint h_path_D
    intro v hv
    exact h_disjoint v hv
  exact ⟨hD.choose, hD.choose_spec.1, h_head_D, h_nodup_D, h_path_lifted⟩

/-! ## Cycle length is bounded by es.length -/

/-- A Nodup list whose elements are all in another list is at most as long. -/
private theorem nodup_subset_length_le
    (A B : List UInt32) (h_nodup : A.Nodup) (h_sub : ∀ a ∈ A, a ∈ B) :
    A.length ≤ B.length := by
  induction A generalizing B with
  | nil => exact Nat.zero_le _
  | cons a rest ih =>
    rw [List.nodup_cons] at h_nodup
    have h_a_notin_rest : a ∉ rest := h_nodup.1
    have h_rest_nodup : rest.Nodup := h_nodup.2
    have h_a_in_B : a ∈ B := h_sub a List.mem_cons_self
    have h_rest_sub_erase : ∀ r ∈ rest, r ∈ B.erase a := by
      intro r hr
      have h_r_in_B : r ∈ B := h_sub r (List.mem_cons_of_mem _ hr)
      have h_r_ne_a : r ≠ a := by
        intro heq; rw [heq] at hr; exact h_a_notin_rest hr
      rw [List.mem_erase_of_ne h_r_ne_a]
      exact h_r_in_B
    have ih' := ih (B.erase a) h_rest_nodup h_rest_sub_erase
    have h_erase_len : (B.erase a).length = B.length - 1 := by
      rw [List.length_erase]; simp [h_a_in_B]
    have h_B_pos : 0 < B.length := by
      cases B with
      | nil => simp at h_a_in_B
      | cons => simp
    simp only [List.length_cons]
    omega

/-- |cycleOf| ≤ |es| because cycleOf is Nodup and each element appears in es as a dst. -/
theorem cycleOf_length_le
    (start : UInt32) (es : Edges) (hC : OnCycle start es) :
    (cycleOf start es hC).length ≤ es.length := by
  unfold cycleOf
  obtain ⟨_, _, h_nodup, h_path⟩ := hC.choose_spec
  -- Build the list of all dsts in es; each cycle element is a dst.
  have h_sub : ∀ a ∈ hC.choose, a ∈ es.map Prod.snd := by
    intro a h_a
    -- a is a node in the cycle. We can show a has a writer in es (by walking back).
    -- For non-last position: writer is path[i+1]; (path[i+1], a) ∈ es.
    -- For last position (a = path.last): writer is start; (start, a) ∈ es.
    obtain ⟨n, h_get⟩ := List.mem_iff_get.mp h_a
    let i := n.val
    have hi : i < hC.choose.length := n.isLt
    have h_get' : hC.choose.get ⟨i, hi⟩ = a := h_get
    by_cases h_last : i + 1 < hC.choose.length
    · have h_walk_eq : walkVisits hC.choose.length start start es = hC.choose :=
        walkVisits_eq_of_onCycle start es hC hC.choose.length (Nat.le_refl _)
      have h_mem_emit :
          (hC.choose.get ⟨i + 1, h_last⟩, hC.choose.get ⟨i, hi⟩) ∈
            walkEmits hC.choose.length start start es := by
        rw [walkEmits_eq_consPairs_walkVisits, h_walk_eq]
        exact consPairs_mem_pair hC.choose i h_last
      have h_in_es : (hC.choose.get ⟨i + 1, h_last⟩, hC.choose.get ⟨i, hi⟩) ∈ es :=
        walkEmits_subset_es _ _ _ _ _ h_mem_emit
      rw [List.mem_map]
      refine ⟨_, h_in_es, ?_⟩
      exact h_get'
    · have h_i_eq : i = hC.choose.length - 1 := by omega
      have h_ne_nil : hC.choose ≠ [] := hC.choose_spec.1
      have h_get_eq_last : hC.choose.get ⟨i, hi⟩ = hC.choose.getLast! :=
        (nodup_get_eq_getLast!_iff hC.choose h_nodup h_ne_nil i hi).mpr h_i_eq
      have h_last_in_es : (start, hC.choose.getLast!) ∈ es :=
        cyclePathTo_last_edge h_path
      rw [List.mem_map]
      refine ⟨_, h_last_in_es, ?_⟩
      rw [← h_get_eq_last]; exact h_get'
  have h_bound : hC.choose.length ≤ (es.map Prod.snd).length :=
    nodup_subset_length_le _ _ h_nodup h_sub
  rw [List.length_map] at h_bound
  exact h_bound

/-! ## walkCycle's outputs are acc-independent (apart from prefix) -/

theorem walkCycle_acc_indep_last
    (fuel : Nat) (start curr : UInt32) (es : Edges)
    (acc : List (Register × Register)) :
    (walkCycle fuel start curr es acc).1 =
      (walkCycle fuel start curr es []).1 := by
  induction fuel generalizing curr es acc with
  | zero => rfl
  | succ n ih =>
    unfold walkCycle
    cases hsrc : srcOf? curr es with
    | none => rfl
    | some source =>
      by_cases h : source = start
      · simp [h]
      · simp [h]
        have h1 := ih source (eraseDst curr es)
            (acc ++ [(Register.given source, Register.given curr)])
        have h2 := ih source (eraseDst curr es)
            [(Register.given source, Register.given curr)]
        exact h1.trans h2.symm

theorem walkCycle_acc_indep_es
    (fuel : Nat) (start curr : UInt32) (es : Edges)
    (acc : List (Register × Register)) :
    (walkCycle fuel start curr es acc).2.1 =
      (walkCycle fuel start curr es []).2.1 := by
  induction fuel generalizing curr es acc with
  | zero => rfl
  | succ n ih =>
    unfold walkCycle
    cases hsrc : srcOf? curr es with
    | none => rfl
    | some source =>
      by_cases h : source = start
      · simp [h]
      · simp [h]
        have h1 := ih source (eraseDst curr es)
            (acc ++ [(Register.given source, Register.given curr)])
        have h2 := ih source (eraseDst curr es)
            [(Register.given source, Register.given curr)]
        exact h1.trans h2.symm

theorem walkCycle_acc_indep_schedule
    (fuel : Nat) (start curr : UInt32) (es : Edges)
    (acc : List (Register × Register)) :
    (walkCycle fuel start curr es acc).2.2 =
      acc ++ (walkCycle fuel start curr es []).2.2 := by
  induction fuel generalizing curr es acc with
  | zero => simp [walkCycle]
  | succ n ih =>
    unfold walkCycle
    split
    · simp
    next source hsrc =>
      split
      · simp [hsrc]
      · -- recurse
        simp only [List.nil_append]
        have hL := ih source (eraseDst curr es)
            (acc ++ [(Register.given source, Register.given curr)])
        have hR := ih source (eraseDst curr es)
            [(Register.given source, Register.given curr)]
        rw [hL, hR]
        simp

/-- `breakOneCycle` with a non-empty acc prepends acc to the schedule produced
    with empty acc. -/
theorem breakOneCycle_schedule_acc_decomp
    (fuel : Nat) (start : UInt32) (es : Edges)
    (acc : List (Register × Register)) :
    (breakOneCycle fuel .temp start es acc).2 =
      acc ++ (breakOneCycle fuel .temp start es []).2 := by
  unfold breakOneCycle
  simp only [List.nil_append]
  have hSched_acc :=
    walkCycle_acc_indep_schedule fuel start start es
      (acc ++ [(Register.given start, Register.temp)])
  have hSched_empty :=
    walkCycle_acc_indep_schedule fuel start start es
      ([(Register.given start, Register.temp)])
  have hLast_acc :=
    walkCycle_acc_indep_last fuel start start es
      (acc ++ [(Register.given start, Register.temp)])
  have hLast_empty :=
    walkCycle_acc_indep_last fuel start start es
      ([(Register.given start, Register.temp)])
  rw [hSched_acc, hSched_empty, hLast_acc, hLast_empty]
  simp [List.append_assoc]

theorem breakOneCycle_residual_acc_indep
    (fuel : Nat) (start : UInt32) (es : Edges)
    (acc : List (Register × Register)) :
    (breakOneCycle fuel .temp start es acc).1 =
      (breakOneCycle fuel .temp start es []).1 := by
  unfold breakOneCycle
  simp only [List.nil_append]
  have h1 := walkCycle_acc_indep_es fuel start start es
      (acc ++ [(Register.given start, Register.temp)])
  have h2 := walkCycle_acc_indep_es fuel start start es
      ([(Register.given start, Register.temp)])
  exact h1.trans h2.symm

/-! ## Filter preserves structural invariants -/

theorem filter_uniqueDst
    (es : Edges) (p : Edge → Bool) (hWF : UniqueDst es) :
    UniqueDst (es.filter p) := by
  intro s₁ s₂ d hm1 hm2
  exact hWF s₁ s₂ d
    (List.mem_filter.mp hm1).1 (List.mem_filter.mp hm2).1

theorem filter_no_self_loops
    (es : Edges) (p : Edge → Bool) (h : ∀ e ∈ es, e.1 ≠ e.2) :
    ∀ e ∈ es.filter p, e.1 ≠ e.2 :=
  fun e he => h e (List.mem_filter.mp he).1


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
