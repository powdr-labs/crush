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
abbrev Memory := UInt32 → UInt32

/-! ## Sequential spec -/

@[grind]
def FunUpdate {α β} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

def applySequential (tmpInit : UInt32) (copies : Array (Register × Register)) (mem : Memory) : Memory := Id.run do
  let mut tmp := tmpInit
  let mut mem := mem
  for (src, dst) in copies do
    let v := match src with
      | .temp => tmp
      | .given r => mem r
    match dst with
      | .temp => tmp := v
      | .given r => mem := FunUpdate mem r v
  return mem

/-! ## Pre-condition -/

/-- The pre-condition demanded by `sequenceParallelCopies`: every destination
    register that is written by a non-trivial copy (`src ≠ dst`) is written
    by at most one distinct source.

    Self-copies are excluded because the algorithm filters them out, and
    *exact* duplicates `(s, d)` with the same `s` are allowed (the algorithm
    deduplicates them). This is the same contract as the Rust shim. -/
def WellFormed (pairs : Array (UInt32 × UInt32)) : Prop :=
  ∀ s₁ s₂ d : UInt32,
    s₁ ≠ d → s₂ ≠ d → (s₁, d) ∈ pairs → (s₂, d) ∈ pairs → s₁ = s₂

/-- Turn the pairs of assignments into a partial function that maps destination to source. -/
def sourceOf (pairs : Array (UInt32 × UInt32)) (d : UInt32) : Option UInt32 :=
  match pairs.find? (fun e => e.2 == d && e.1 != e.2) with
  | some (s, _) => some s
  | none => none

/-- After specifying `sourceOf` constructively, verify that it actually does what we want. -/
@[grind =]
theorem sourceOf_correct (pairs : Array (UInt32 × UInt32)) (h_wf : WellFormed pairs) :
  ∀ s d, sourceOf pairs d = some s ↔ (s, d) ∈ pairs ∧ s ≠ d := by
  intros s d
  unfold sourceOf
  constructor
  · intro h
    grind
  · intro ⟨hmem, hsne⟩
    cases hfind : pairs.find? (fun e => e.2 == d && e.1 != e.2) with
    | none => grind
    | some pair =>
      rcases pair with ⟨s0, d0⟩
      have : s0 = s := h_wf s0 s d (by grind) hsne (by grind) hmem
      grind

def applyParallel (pairs : Array (UInt32 × UInt32)) (mem : Memory) : Memory :=
  fun addr =>
    match sourceOf pairs addr with
    | some s => mem s
    | none => mem addr

/-! ## Correctness statement -/
def RealisesParallel
    (impl : Array (UInt32 × UInt32) → Array (Register × Register)) : Prop :=
  ∀ (pairs : Array (UInt32 × UInt32)), WellFormed pairs →
    ∀ tmpInit,
    applySequential tmpInit (impl pairs) = applyParallel pairs

end ParallelCopies.Spec
