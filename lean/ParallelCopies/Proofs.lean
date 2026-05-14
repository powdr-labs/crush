import ParallelCopies.SpecLemmas

/-!
# Algorithm-level proofs

This file is the home for proofs about the actual two-phase algorithm in
`ParallelCopies.lean` against the semantic spec in `ParallelCopies.Spec`.

The eventual goal is

    theorem sequenceParallelCopies_correct :
        Spec.RealisesParallel sequenceParallelCopies

i.e. for every well-formed input and every initial state, executing the
sequenced output on the lifted state agrees with `applyParallel` on every
concrete register.

## What's proved here

* **`buildGraph_nil`** — the algorithm's graph builder produces the empty
  graph on empty input.
* **`leavesOf_empty`**, **`smallestKey?_empty`** — fold-on-empty equations
  for the two HashMap sweeps used by the algorithm.
* **`pruneTrees_no_leaves`**, **`breakCycles_empty`** — base cases for the
  two phase drivers.
* **`sequenceParallelCopies_nil`** — the algorithm returns the empty
  sequence on empty input.  Combined with `applyParallel_nil`, this proves
  `RealisesParallel` for empty inputs.
* **`sequenceParallelCopies_correct_on_empty`** — the cleanest end-to-end
  correctness statement we can close at this stage: on `#[]` the algorithm
  matches the parallel spec for every initial state and every register.

## What's *not* here yet, and why

Closing the full `sequenceParallelCopies_correct` on non-empty inputs
requires significant additional infrastructure:

1. More `Std.HashMap` soundness lemmas (insert/erase/getD under various
   invariants); Lean 4.29's stdlib doesn't ship clean rewrite forms.
2. An invariant threaded through `pruneTrees`: at every step the live
   sub-state still realises the *residual* parallel block.
3. The cycle-breaking soundness lemma for `walkCycle`/`breakOneCycle`:
   spilling the cycle's start to a temp, walking sources backwards, then
   restoring from the temp implements the parallel rotation.
4. Concatenation: combining the per-phase invariants via
   `applySequential_append`.

Each step is tractable but together they're a substantial proof project
(comparable in size to the executable port itself).
-/

namespace ParallelCopies

open Spec

/-! ## HashMap fold-on-empty equations -/

/-- `leavesOf` of the empty graph is the empty array. -/
@[simp] theorem leavesOf_empty : leavesOf (∅ : Graph) = #[] := by
  simp [leavesOf, Std.HashMap.fold_eq_foldl_toList]

/-- `smallestKey?` of the empty graph is `none`. -/
@[simp] theorem smallestKey?_empty : smallestKey? (∅ : Graph) = none := by
  simp [smallestKey?, Std.HashMap.fold_eq_foldl_toList]

/-! ## Graph builder on empty input -/

/-- `buildGraph #[] = ∅`. -/
@[simp] theorem buildGraph_nil : buildGraph #[] = (∅ : Graph) := by
  unfold buildGraph; rfl

/-! ## Phase drivers on degenerate inputs -/

/-- `pruneTrees` with no leaves to process returns immediately. -/
@[simp] theorem pruneTrees_no_leaves
    (fuel : Nat) (g : Graph) (acc : Array (UInt32 × UInt32)) :
    pruneTrees fuel g #[] acc = (g, acc) := by
  cases fuel <;> simp [pruneTrees]

/-- `breakCycles` on the empty graph returns the accumulator unchanged. -/
@[simp] theorem breakCycles_empty
    (fuel : Nat) (tmp : Register) (acc : Array (Register × Register)) :
    breakCycles fuel tmp ∅ acc = acc := by
  cases fuel <;> simp [breakCycles]

/-! ## Top-level: empty input -/

/-- The flagship base case: empty input produces the empty schedule. -/
@[simp] theorem sequenceParallelCopies_nil :
    sequenceParallelCopies #[] = #[] := by
  unfold sequenceParallelCopies
  simp

/-- End-to-end correctness on empty input: the algorithm's output, executed
    on any initial state, agrees with the parallel spec on every
    concrete register. -/
theorem sequenceParallelCopies_correct_on_empty
    (s : State) (r : UInt32) :
    applySequential (sequenceParallelCopies #[]) (lift s) (.given r) =
      applyParallel #[] s r := by
  simp

end ParallelCopies

