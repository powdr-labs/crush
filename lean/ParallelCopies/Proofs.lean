import ParallelCopies.SpecLemmas

/-!
# Algorithm-level proofs

Correctness proof for `sequenceParallelCopies` against the spec defined in
`ParallelCopies.Spec`.

The proof is structured as follows:

1.  **Preprocessing** (`preprocess`) removes self-copies and exact duplicates
    while preserving the *semantics* of `applyParallel`.
2.  **Phase 1 invariant.** Throughout phase 1, the *concatenation* of the
    emitted copies and a fresh parallel application of the residual graph
    matches the parallel application of the original input. The crucial
    local lemma is that one `peelStep` preserves this invariant: the
    source-swap is sound because, after emitting `(src, dst)`, register
    `dst` already holds `src`'s pre-copy value.
3.  **Phase 1 termination.** Phase 1 produces a residual graph in which no
    register is a leaf — i.e., every remaining destination is also a source.
    Such a graph is a disjoint union of pure cycles.
4.  **Phase 2 invariant.** `walkCycle` over a single cycle followed by
    closing with `(tmp, last)` produces a sequential schedule equivalent to
    parallel application of that cycle.
5.  **Composition.** Sequential application of (phase 2 copies) ++ (phase 1
    copies) equals parallel application of the original.

The proof currently captures the base cases and the spec-level lemmas. The
phase-1 source-swap soundness lemma and the phase-2 cycle-walk lemma are
present as named obligations the proof will discharge.
-/

namespace ParallelCopies

open Spec

/-! ## Base cases -/

@[simp] theorem preprocess_nil : preprocess [] = [] := rfl

@[simp] theorem phase1_zero (es : Edges) (acc : List Edge) :
    phase1 0 es acc = (es, acc) := rfl

@[simp] theorem phase2_zero (tmp : Register) (es : Edges)
    (acc : List (Register × Register)) :
    phase2 0 tmp es acc = acc := rfl

@[simp] theorem walkCycle_zero (start curr : UInt32) (es : Edges)
    (acc : List (Register × Register)) :
    walkCycle 0 start curr es acc = (curr, es, acc) := rfl

/-! ## `findLeafEdge` on the empty graph -/

@[simp] theorem findLeafEdge_nil : findLeafEdge [] = none := rfl

@[simp] theorem isLeaf_nil (r : UInt32) : isLeaf r [] = true := rfl

@[simp] theorem srcOf?_nil (r : UInt32) : srcOf? r [] = none := rfl

@[simp] theorem eraseDst_nil (r : UInt32) : eraseDst r [] = [] := rfl

@[simp] theorem smallestDst_nil : smallestDst [] = none := rfl

@[simp] theorem peelStep_nil (s d : UInt32) : peelStep s d [] = [] := rfl

/-! ## Empty phase 1 / 2 -/

@[simp] theorem phase1_no_leaf (n : Nat) (es : Edges) (acc : List Edge)
    (h : findLeafEdge es = none) :
    phase1 (n + 1) es acc = (es, acc) := by
  simp [phase1, h]

@[simp] theorem phase1_nil (n : Nat) (acc : List Edge) :
    phase1 n [] acc = ([], acc) := by
  cases n
  · simp
  · simp [phase1]

@[simp] theorem phase2_nil (n : Nat) (tmp : Register)
    (acc : List (Register × Register)) :
    phase2 n tmp [] acc = acc := by
  cases n
  · simp
  · simp [phase2]

/-! ## Top-level on empty input -/

@[simp] theorem sequenceParallelCopiesL_nil :
    sequenceParallelCopiesL [] = [] := by
  simp [sequenceParallelCopiesL]

@[simp] theorem sequenceParallelCopies_empty :
    sequenceParallelCopies #[] = #[] := by
  simp [sequenceParallelCopies]

/-- End-to-end correctness on empty input. -/
theorem sequenceParallelCopies_correct_on_empty
    (s : State) (r : UInt32) :
    applySequential (sequenceParallelCopies #[]) (lift s) (.given r) =
      applyParallel #[] s r := by
  simp

end ParallelCopies
