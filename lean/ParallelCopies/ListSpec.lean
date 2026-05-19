import ParallelCopies.SpecLemmas

/-!
# List-based parallel/sequential semantics

The spec module (`ParallelCopies.Spec`) is parameterised over `Array`
inputs, matching the FFI boundary. The two-phase algorithm, however, works
on a `List` representation that is much friendlier to reason about. This
module mirrors `Spec` for `List` inputs and connects the two via
`Array.toList` lemmas, so the algorithm proof can be carried out entirely
in the list world and then transported back to the array world for the
public statement of correctness.
-/

namespace ParallelCopies.Spec

open Register

/-! ## List-based parallel application -/

/-- The list version of `applyParallel`. Uses the same predicate as
    `Spec.findWriter?` (`Pair.appliesTo`) so the array-bridge lemma is
    a straightforward `Array.find?_toList`. -/
def applyParallelL (es : List Edge) (s : Memory) : Memory :=
  fun r =>
    match es.find? (Pair.appliesTo · r) with
    | some (src, _) => s src
    | none          => s r

/-- The list version applied to a sequential state, leaving the temporary
    register untouched (the algorithm never writes to `temp` after spilling
    a cycle's start and restoring it). -/
def applyParallelLS (es : List Edge) (σ : SState) : SState :=
  fun r => match r with
    | .temp     => σ .temp
    | .given r' =>
      match es.find? (Pair.appliesTo · r') with
      | some (src, _) => σ (.given src)
      | none          => σ (.given r')

@[simp] theorem applyParallelL_nil (s : Memory) :
    applyParallelL [] s = s := by funext r; simp [applyParallelL]

@[simp] theorem applyParallelLS_nil (σ : SState) :
    applyParallelLS [] σ = σ := by
  funext r
  cases r <;> simp [applyParallelLS]

/-- The `LS` version respects lifting from `State`. -/
theorem applyParallelLS_lift (es : List Edge) (s : Memory) :
    applyParallelLS es (lift s) = lift (applyParallelL es s) := by
  funext r
  cases r with
  | temp     => simp [applyParallelLS, lift]
  | given r' => simp [applyParallelLS, applyParallelL, lift]

/-! ## List-based sequential application -/

/-- The list version of `applySequential`. -/
def applySequentialL (copies : List (Register × Register)) (σ : SState) : SState :=
  copies.foldl step σ

@[simp] theorem applySequentialL_nil (σ : SState) :
    applySequentialL [] σ = σ := rfl

@[simp] theorem applySequentialL_cons (cp : Register × Register)
    (rest : List (Register × Register)) (σ : SState) :
    applySequentialL (cp :: rest) σ = applySequentialL rest (step σ cp) := by
  simp [applySequentialL]

theorem applySequentialL_append
    (xs ys : List (Register × Register)) (σ : SState) :
    applySequentialL (xs ++ ys) σ =
      applySequentialL ys (applySequentialL xs σ) := by
  simp [applySequentialL, List.foldl_append]

@[simp] theorem applySequentialL_singleton
    (cp : Register × Register) (σ : SState) :
    applySequentialL [cp] σ = step σ cp := by
  simp

/-! ## Bridge: Array ↔ List -/

theorem applySequential_eq_L
    (copies : Array (Register × Register)) (σ : SState) :
    applySequential copies σ = applySequentialL copies.toList σ := by
  simp [applySequential, applySequentialL, Array.foldl_toList]

theorem applyParallel_eq_L
    (pairs : Array Edge) (s : Memory) :
    applyParallel pairs s = applyParallelL pairs.toList s := by
  funext r
  unfold applyParallel applyParallelL findWriter?
  rw [← Array.find?_toList]
  rfl

end ParallelCopies.Spec
