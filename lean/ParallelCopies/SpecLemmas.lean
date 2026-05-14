import ParallelCopies.Spec

/-!
# Lemmas about the parallel/sequential specs

Everything here is about the *spec* (`applyParallel`, `applySequential`) and
is independent of the actual two-phase algorithm. These lemmas form the
algebraic foundation the algorithm correctness proof will build on.
-/

namespace ParallelCopies.Spec

open Register

/-! ## `findWriter?` lemmas -/

@[simp] theorem findWriter?_nil (r : UInt32) :
    findWriter? #[] r = none := by
  simp [findWriter?]

theorem findWriter?_singleton (src dst r : UInt32) :
    findWriter? #[(src, dst)] r =
      (if Pair.appliesTo (src, dst) r then some (src, dst) else none) := by
  simp [findWriter?]

/-! ## `Pair.appliesTo` lemmas -/

/-- A pair `(r, r)` never *applies to* any register (it's a self-copy). -/
@[simp] theorem Pair.appliesTo_self_lhs (r q : UInt32) :
    Pair.appliesTo (r, r) q = false := by
  simp [Pair.appliesTo]

/-- A non-self-copy `(src, dst)` does apply to its destination `dst`. -/
theorem Pair.appliesTo_dst_of_ne {src dst : UInt32} (h : src ≠ dst) :
    Pair.appliesTo (src, dst) dst = true := by
  simp only [Pair.appliesTo, bne, beq_self_eq_true, Bool.true_and]
  rcases Decidable.em (src = dst) with heq | hne
  · exact absurd heq h
  · simp [hne]

/-- A pair never applies to a register other than its destination. -/
theorem Pair.appliesTo_of_ne_dst {src dst r : UInt32} (h : r ≠ dst) :
    Pair.appliesTo (src, dst) r = false := by
  simp only [Pair.appliesTo, Bool.and_eq_false_iff]
  left
  rcases Decidable.em (dst = r) with heq | hne
  · exact absurd heq.symm h
  · simp [hne]

/-! ## `applyParallel`: basic identities -/

/-- Applying an empty list of parallel copies is the identity. -/
@[simp] theorem applyParallel_nil (s : State) :
    applyParallel #[] s = s := by
  funext r
  simp [applyParallel]

/-- Applying a single non-self-copy writes the source's *original* value to
    the destination, and leaves every other register unchanged. -/
theorem applyParallel_single
    {src dst : UInt32} (hne : src ≠ dst) (s : State) :
    applyParallel #[(src, dst)] s =
      fun r => if r = dst then s src else s r := by
  funext r
  unfold applyParallel
  rw [findWriter?_singleton]
  by_cases h : r = dst
  · subst h
    rw [Pair.appliesTo_dst_of_ne hne]
    simp
  · rw [Pair.appliesTo_of_ne_dst h]
    simp [h]

/-- A single self-copy is a no-op. -/
@[simp] theorem applyParallel_selfCopy (r : UInt32) (s : State) :
    applyParallel #[(r, r)] s = s := by
  funext q
  unfold applyParallel
  rw [findWriter?_singleton, Pair.appliesTo_self_lhs]
  simp

/-! ## `applySequential`: basic identities -/

/-- Applying an empty sequence of copies is the identity. -/
@[simp] theorem applySequential_nil (s : SState) :
    applySequential #[] s = s := by
  simp [applySequential]

/-- A single sequential copy is exactly `step`. -/
@[simp] theorem applySequential_singleton (cp : Register × Register) (s : SState) :
    applySequential #[cp] s = step s cp := by
  simp [applySequential]

/-- Sequential composition: applying `xs ++ ys` is applying `xs` then `ys`. -/
theorem applySequential_append
    (xs ys : Array (Register × Register)) (s : SState) :
    applySequential (xs ++ ys) s =
      applySequential ys (applySequential xs s) := by
  simp [applySequential]

/-- The destination written by a copy holds the source's pre-copy value. -/
@[simp] theorem step_dst (s : SState) (cp : Register × Register) :
    step s cp cp.2 = s cp.1 := by
  simp [step]

/-- Every register *other than* the destination of a copy is left alone. -/
theorem step_other (s : SState) (cp : Register × Register) {r : Register}
    (h : r ≠ cp.2) : step s cp r = s r := by
  simp [step, h]

/-! ## `lift`: the embedding from concrete state to sequential state -/

@[simp] theorem lift_given (s : State) (tmp : UInt32) (r : UInt32) :
    lift s tmp (.given r) = s r := rfl

@[simp] theorem lift_temp (s : State) (tmp : UInt32) :
    lift s tmp .temp = tmp := rfl

/-! ## Putting it together: a sanity-check theorem -/

/-- For empty input, the empty implementation already realises `applyParallel`.
    Sanity check that our framing is right. -/
theorem realisesParallel_emptyImpl_on_empty
    (s : State) (r : UInt32) :
    applySequential #[] (lift s) (Register.given r) = applyParallel #[] s r := by
  simp

end ParallelCopies.Spec
