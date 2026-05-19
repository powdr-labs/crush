import Std.Data.HashSet.Basic
import Std.Data.TreeMap.Basic
import Std.Data.TreeSet.Basic
/-!
# Parallel-Copy Sequencing — verified Lean 4 implementation

A port of `crush::loader::rwm::flattening::sequence_parallel_copies` to Lean 4.

Given a set of *parallel* assignments `dst_i := src_i` with at most one source
per destination, produce a sequential schedule of register copies with at most
one extra temporary register that has the same post-state as the parallel
assignment.

The algorithm has two phases:

* **Phase 1 — prune trees.** A *leaf* is a destination that is not itself a
  source. Emit `(src(leaf), leaf)`, then update the graph by *source-swapping*:
  the leaf takes over the source's remaining out-edges. This naturally severs
  any cycle that has a tree hanging off it, so after phase 1 only pure cycles
  remain.

* **Phase 2 — break remaining cycles.** Save each cycle's starting register
  into a single temporary, walk the cycle emitting intra-cycle copies, then
  close it with `temp → last`.

## Data structures

The graph is represented as a pair of balanced search trees:

* `dstToSrc : Std.TreeMap UInt32 UInt32` — destination ↦ source. Each edge
  `(s, d)` appears as `d ↦ s`. Unique destinations are enforced by the
  precondition.
* `srcToDsts : Std.TreeMap UInt32 (Std.TreeSet UInt32)` — source ↦ set of
  destinations it writes to. A source with no outgoing edges has no entry.

Together with a `LeafSet` (destinations not currently in `srcToDsts`), all
graph operations run in `O(log n)` and the schedule is fully deterministic:
Phase 1 always peels the smallest available leaf, Phase 2 always starts
each cycle at its smallest destination. Total: `O(n log n)`.

We choose trees over hash tables because hash iteration order is sensitive
to the hash function and resize history; using `Std.HashMap` here would make
the emitted schedule non-deterministic across runs. (`preprocess` still uses
`Std.HashSet` for dedup — it iterates the *input array* in fixed order, so
the dedup is order-independent.)
-/

namespace ParallelCopies

/-- An output register: either the dedicated temporary used to break cycles,
    or one of the original registers carried over from the input. -/
inductive Register
  | temp
  | given (r : UInt32)
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

/-- An edge `(src, dst)` of the copy graph: the value at `src` should end up
    at `dst`. -/
abbrev Edge := UInt32 × UInt32

/-! ## Graph data structures -/

/-- Destination ↦ source. -/
abbrev DstMap := Std.TreeMap UInt32 UInt32
/-- Source ↦ set of destinations it writes to. -/
abbrev SrcMap := Std.TreeMap UInt32 (Std.TreeSet UInt32)
/-- Destinations that are not currently sources of any remaining edge. -/
abbrev LeafSet := Std.TreeSet UInt32

/-! ## Phase 0 — preprocessing -/

/-- Drop self-copies and exact duplicates while preserving the order of first
    occurrence. -/
def preprocess (edges : Array Edge) : Array Edge := Id.run do
  let mut seen : Std.HashSet Edge := {}
  let mut result := #[]
  for e in edges do
    if e.1 == e.2 then
      continue
    else if seen.contains e then
      continue
    else
      seen := seen.insert e
      result := result.push e
  return result

/-! ## Graph construction -/

/-- Build the `(dstToSrc, srcToDsts)` pair from a preprocessed edge array. -/
def buildGraph (edges : Array Edge) : DstMap × SrcMap := Id.run do
  let mut d2s : DstMap := ∅
  let mut s2d : SrcMap := ∅
  for (s, d) in edges do
    d2s := d2s.insert d s
    let outs := s2d.getD s ∅
    s2d := s2d.insert s (outs.insert d)
  return (d2s, s2d)

/-- Initial set of leaves: destinations of `d2s` that are not in `s2d`. -/
def initLeaves (d2s : DstMap) (s2d : SrcMap) : LeafSet := Id.run do
  let mut leaves : LeafSet := ∅
  for (d, _) in d2s do
    if !s2d.contains d then
      leaves := leaves.insert d
  return leaves

/-! ## Phase 1 — prune trees -/

/-- Phase-1 driver. Peels the smallest available leaf each iteration; emits
    `(src, dst)` in peel order, source-swaps the rewires, and propagates new
    leaves. Fuel-bounded for trivial termination; `fuel ≥ |edges|` suffices.

    Returns the cycle-only residue (in `dstToSrc`) and the array of emitted
    non-cycle copies. -/
def phase1 : Nat → DstMap → SrcMap → LeafSet → Array Edge → DstMap × Array Edge
  | 0,    d2s, _,   _,      acc => (d2s, acc)
  | n+1,  d2s, s2d, leaves, acc =>
    match leaves.min? with
    | none => (d2s, acc)
    | some d =>
      match d2s.get? d with
      | none =>
        -- Stale leaf entry (invariant temporarily broken); drop it and retry.
        phase1 n d2s s2d (leaves.erase d) acc
      | some s =>
        let acc          := acc.push (s, d)
        let d2s          := d2s.erase d
        let sOuts        := s2d.getD s ∅
        let sOutsMinusD  := sOuts.erase d
        let s2d          := s2d.erase s
        -- Rewire each remaining `(s, x)` to `(d, x)` by updating `dstToSrc`.
        let d2s          := sOutsMinusD.foldl (init := d2s)
                              fun m x => m.insert x d
        -- `d` inherits `s`'s remaining out-edges (if any).
        let s2d          := if sOutsMinusD.isEmpty then s2d
                            else s2d.insert d sOutsMinusD
        let leaves       := leaves.erase d
        -- `s` may now be a leaf: it is no longer a source, and may still be
        -- a destination of some other edge.
        let leaves       := if d2s.contains s && !s2d.contains s
                            then leaves.insert s else leaves
        phase1 n d2s s2d leaves acc

/-! ## Phase 2 — break remaining cycles -/

/-- Walk one cycle from `curr`, emitting `(src, curr)` register copies and
    erasing the edge writing to `curr`. When the source of `curr` is the
    original `start`, emit `(tmp, curr)` and stop. Fuel-bounded. -/
def walkCycle :
    Nat → DstMap → UInt32 → UInt32 → Array (Register × Register)
      → DstMap × Array (Register × Register)
  | 0,    d2s, _,     _,    acc => (d2s, acc)
  | n+1,  d2s, start, curr, acc =>
    match d2s.get? curr with
    | none => (d2s, acc)
    | some src =>
      let d2s := d2s.erase curr
      if src == start then
        (d2s, acc.push (.temp, .given curr))
      else
        walkCycle n d2s start src (acc.push (.given src, .given curr))

/-- Phase-2 driver: drain every remaining cycle, starting each cycle at its
    smallest destination. Fuel-bounded. -/
def phase2 : Nat → DstMap → Array (Register × Register) → Array (Register × Register)
  | 0,    _,   acc => acc
  | n+1,  d2s, acc =>
    match d2s.minKey? with
    | none       => acc
    | some start =>
      -- Spill: `tmp := start`, then walk the cycle.
      let acc          := acc.push (.given start, .temp)
      let (d2s, acc)   := walkCycle n d2s start start acc
      phase2 n d2s acc

/-! ## Top-level entry point -/

/-- Sequence parallel copies into a sequential schedule with at most one
    temporary. **Pre-condition**: every destination register appears at most
    once as a non-self-copy destination. -/
def sequenceParallelCopies (pairs : Array Edge) : Array (Register × Register) :=
  let es              := preprocess pairs
  let (d2s, s2d)      := buildGraph es
  let leaves          := initLeaves d2s s2d
  let fuel            := es.size + 1
  let (d2s, nonCycle) := phase1 fuel d2s s2d leaves #[]
  let nonCycleRegs    := nonCycle.map fun (s, d) =>
                          (Register.given s, Register.given d)
  nonCycleRegs ++ phase2 fuel d2s #[]

/-! ## FFI surface

The C bridge passes packed little-endian byte streams across the boundary:

* Input  : `[src₀, dst₀, src₁, dst₁, …]` — `UInt32` pairs.
* Output : `[tag_s, val_s, tag_d, val_d, …]` per emitted copy.
  `tag = 0` means `Register.temp` (and `val` is unused); `tag = 1` means
  `Register.given val`.
-/

def readU32LE (bs : ByteArray) (off : Nat) : UInt32 :=
  let byte (i : Nat) : UInt32 := (bs.get! (off + i)).toUInt32
  byte 0 ||| (byte 1 <<< 8) ||| (byte 2 <<< 16) ||| (byte 3 <<< 24)

def pushU32LE (bs : ByteArray) (x : UInt32) : ByteArray :=
  [0, 8, 16, 24].foldl (init := bs) fun bs shift =>
    bs.push ((x >>> shift.toUInt32) &&& 0xff).toUInt8

def encodeRegister : Register → UInt32 × UInt32
  | .temp    => (0, 0)
  | .given r => (1, r)

def decodePairs (bytes : ByteArray) : Array Edge :=
  let n := bytes.size / 8
  (Array.range n).map fun i =>
    let off := i * 8
    (readU32LE bytes off, readU32LE bytes (off + 4))

def encodeCopies (copies : Array (Register × Register)) : ByteArray :=
  copies.foldl (init := ByteArray.empty) fun bs (a, b) =>
    let (ta, va) := encodeRegister a
    let (tb, vb) := encodeRegister b
    [ta, va, tb, vb].foldl pushU32LE bs

/-- FFI entry point. The argument is consumed (Lean's RC decrements it
    inside the generated wrapper after `decodePairs`), so the C bridge
    must not `lean_dec_ref` it explicitly. -/
@[export rust_seq_parallel_copies]
def rustSeqParallelCopies (input : ByteArray) : ByteArray :=
  encodeCopies (sequenceParallelCopies (decodePairs input))

end ParallelCopies
