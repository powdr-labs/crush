import ParallelCopies

/-!
# Semantic spec for parallel-copy sequencing

This module gives a precise mathematical meaning to two operations and states
the correctness theorem that ties them together.

* `applyParallel` is the *spec* for a parallel assignment block:
  every destination receives the value its source held **before** the block,
  with self-copies and exact duplicates filtered out.

* `applySequential` is the obvious sequential interpreter for the output of
  `sequenceParallelCopies`: write `dst := src` one copy at a time.

The main correctness theorem to prove is `RealisesParallel sequenceParallelCopies`
(see the definition below); the trivial "save-then-restore" implementation
satisfies it, but proving that the real two-phase algorithm does is the
central verification goal.
-/

namespace ParallelCopies.Spec

/-! ## State -/

/-- The state visible to the parallel block: a total function from concrete
    register indices to their stored value. -/
abbrev State := UInt32 → UInt32

/-- The state visible to the sequential interpreter, which also tracks the
    contents of the cycle-breaking temporary register. -/
abbrev SState := Register → UInt32

/-- Lift a concrete state into the sequential world. The temporary register
    starts holding `tmp` (default `0` — its initial value is irrelevant since
    no copy ever reads `temp` before writing it). -/
def lift (s : State) (tmp : UInt32 := 0) : SState
  | .temp     => tmp
  | .given r  => s r

/-! ## Parallel spec -/

/-- A pair *applies to* register `r` if it writes a non-self-copied value
    into `r`. -/
@[simp] def Pair.appliesTo (p : UInt32 × UInt32) (r : UInt32) : Bool :=
  p.2 == r && p.1 != p.2

/-- Search the pair list for one that writes to `r`. Because the pre-condition
    bans two pairs from writing the same destination, at most one such pair
    exists in a well-formed input. -/
def findWriter? (pairs : Array (UInt32 × UInt32)) (r : UInt32)
    : Option (UInt32 × UInt32) :=
  pairs.find? (Pair.appliesTo · r)

/-- Apply the parallel block to a state. Every output register `r` reads its
    new value from the *original* state: either from the source named by the
    unique pair writing into `r`, or — when no such pair exists — from `r`
    itself (unchanged). -/
def applyParallel (pairs : Array (UInt32 × UInt32)) (s : State) : State :=
  fun r =>
    match findWriter? pairs r with
    | some (src, _) => s src
    | none          => s r

/-! ## Sequential spec -/

/-- Update a state with a single copy `dst := src`. -/
@[simp] def step (s : SState) (copy : Register × Register) : SState :=
  fun r => if r = copy.2 then s copy.1 else s r

/-- Apply a sequence of copies left-to-right. Built on `Array.foldl` so that
    proofs can reuse the standard `foldl` lemmas. -/
def applySequential (copies : Array (Register × Register)) (s : SState) : SState :=
  copies.foldl step s

/-! ## Pre-condition -/

/-- The pre-condition demanded by `sequenceParallelCopies`: every destination
    register that is written by a non-trivial copy (`src ≠ dst`) is written
    by at most one distinct source.

    Self-copies are excluded because the algorithm filters them out, and
    *exact* duplicates `(s, d)` with the same `s` are allowed (the algorithm
    deduplicates them). This is the same contract as the Rust shim. -/
def WellFormed (pairs : Array (UInt32 × UInt32)) : Prop :=
  ∀ s₁ s₂ d : UInt32,
    s₁ ≠ d → s₂ ≠ d →
    (s₁, d) ∈ pairs.toList → (s₂, d) ∈ pairs.toList → s₁ = s₂

/-! ## Correctness statement

    The full correctness claim, parameterised over an implementation
    `impl : Array (UInt32 × UInt32) → Array (Register × Register)`.
    `RealisesParallel impl` says: for every well-formed input and every
    initial state, the sequential output sequence — when executed on the
    lifted state — leaves every concrete register holding the value the
    parallel spec demands. The temporary register's final contents are
    irrelevant. -/
def RealisesParallel
    (impl : Array (UInt32 × UInt32) → Array (Register × Register)) : Prop :=
  ∀ (pairs : Array (UInt32 × UInt32)),
    WellFormed pairs →
    ∀ (s : State) (r : UInt32),
      applySequential (impl pairs) (lift s) (.given r) =
      applyParallel pairs s r

end ParallelCopies.Spec
