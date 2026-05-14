import Std.Data.HashMap

/-!
# Parallel-Copy Sequencing

A port of `crush::loader::rwm::flattening::sequence_parallel_copies` to Lean 4.

Given a set of *parallel* assignments `dst_i := src_i` with a unique destination
for each pair, produce a sequential schedule of register copies with at most one
extra temporary register that has the same post-state as the parallel assignment.

The implementation follows the same two-phase algorithm as the Rust source:

* **Phase 1** — repeatedly emit a copy whose destination is a graph "leaf"
  (a register that is not itself a source). Removing the edge from its source
  and source-swapping the source's remaining out-edges naturally breaks any
  cycle that has a tree hanging off it, so after this phase the graph contains
  only pure cycles.

* **Phase 2** — break each remaining pure cycle with a single temporary.
  The temporary is either the destination of the very first non-cycle copy
  (which by then already holds a value we can clobber), or — when there were
  no non-cycle copies at all — a dedicated `Register.temp`.

The phase-2 copies are emitted *before* the phase-1 copies so that the
temporary register is not overwritten by them.
-/

namespace ParallelCopies

/-- An output register: either the dedicated temporary used to break cycles,
    or one of the original registers carried over from the input. -/
inductive Register where
  | temp
  | given (r : UInt32)
  deriving Repr, BEq, Hashable, Inhabited

/-- Adjacency record for a single register node in the copy graph. -/
structure RegConn where
  /-- The (unique) register whose value is copied *into* this one, if any. -/
  src  : Option UInt32 := none
  /-- The registers that this one is copied *into*. -/
  dest : Array UInt32  := #[]
  deriving Inhabited

private abbrev Graph := Std.HashMap UInt32 RegConn

/-! ## Phase 0 — graph construction -/

/-- Build the copy graph, enforcing the pre-condition that every destination
    register is written to at most once. Self-copies and exact duplicates are
    silently dropped. -/
private def buildGraph (pairs : Array (UInt32 × UInt32)) : Graph := Id.run do
  let mut g : Graph := ∅
  for (src, dst) in pairs do
    if src == dst then
      continue
    let dstE := g.getD dst {}
    match dstE.src with
    | some s =>
      if s == src then
        continue
      else
        panic! s!"Pre-condition violated: destination register {dst} is written to more than once"
    | none => pure ()
    g := g.insert dst { dstE with src := some src }
    let srcE := g.getD src {}
    g := g.insert src { srcE with dest := srcE.dest.push dst }
  return g

/-! ## Phase 1 — prune trees -/

/-- Collect every register in the graph that has no outgoing edges; these are
    the "leaves" we can immediately copy into without overwriting a future read. -/
private def initialLeaves (g : Graph) : Array UInt32 :=
  g.fold (init := (#[] : Array UInt32)) fun acc reg conn =>
    if conn.dest.isEmpty then acc.push reg else acc

/-- Phase 1 body: pop a leaf, emit `(source, target)`, then update the graph.

    The key step is *source-swapping*: after `target` receives `source`'s value
    it becomes the new source for any of `source`'s other out-edges. This is
    what breaks cycles that have a tree attached to them — the cycle is
    silently severed when `target` takes over. -/
private partial def pruneTrees
    (g₀ : Graph) (leaves₀ : Array UInt32)
    : Graph × Array (UInt32 × UInt32) := Id.run do
  let mut g       := g₀
  let mut leaves  := leaves₀
  let mut copies  : Array (UInt32 × UInt32) := #[]
  while !leaves.isEmpty do
    let target := leaves.back!
    leaves := leaves.pop
    let source := (g.get! target).src.get!
    copies := copies.push (source, target)
    -- Remove the edge source → target.
    let srcN0 := g.get! source
    let pruned := srcN0.dest.filter (· != target)
    -- After taking target's edge out, the remaining out-edges of `source`
    -- now belong to `target` (the source-swap).
    if srcN0.src.isNone then
      g := g.erase source
    else
      g := g.insert source { srcN0 with dest := #[] }
      leaves := leaves.push source
    if pruned.isEmpty then
      g := g.erase target
    else
      for d in pruned do
        let dE := g.get! d
        g := g.insert d { dE with src := some target }
      g := g.insert target { src := none, dest := pruned }
  return (g, copies)

/-! ## Phase 2 — break remaining cycles -/

/-- The smallest key in a non-empty graph. Iteration over `Std.HashMap` is
    unordered, so we sweep the keys ourselves to keep the output deterministic. -/
private def smallestKey (g : Graph) : UInt32 := Id.run do
  let mut best : Option UInt32 := none
  for k in g.keys do
    match best with
    | none   => best := some k
    | some b => if k < b then best := some k
  best.get!

/-- Phase 2 body: every remaining connected component is a single pure cycle.
    Break each by routing the initial value through `tmpReg`. -/
private partial def breakCycles
    (g₀ : Graph) (tmpReg : Register)
    : Array (Register × Register) := Id.run do
  let mut g     := g₀
  let mut out   : Array (Register × Register) := #[]
  while !g.isEmpty do
    let initial := smallestKey g
    out := out.push (Register.given initial, tmpReg)
    let mut curr := initial
    let mut walking := true
    while walking do
      let node   := g.get! curr
      let source := node.src.get!
      g := g.erase curr
      if source == initial then
        walking := false
      else
        out := out.push (Register.given source, Register.given curr)
        curr := source
    out := out.push (tmpReg, Register.given curr)
  return out

/-! ## Top-level entry point -/

/-- Sequence a set of parallel copies into a list of sequential copies that
    preserves the parallel-assignment semantics, using at most one temporary.

    **Pre-condition**: every destination register appears at most once. -/
def sequenceParallelCopies
    (pairs : Array (UInt32 × UInt32)) : Array (Register × Register) :=
  let g₀ := buildGraph pairs
  let (g₁, nonCycle) := pruneTrees g₀ (initialLeaves g₀)
  let tmpReg : Register :=
    match nonCycle[0]? with
    | some (_, dst) => Register.given dst
    | none          => Register.temp
  breakCycles g₁ tmpReg
    ++ nonCycle.map (fun (s, d) => (Register.given s, Register.given d))

/-! ## FFI surface -/

/-! Encoding used across the C boundary:
* Input  : raw little-endian `[src₀, dst₀, src₁, dst₁, …]` as `UInt32` pairs.
* Output : raw little-endian `[tag_src, val_src, tag_dst, val_dst, …]`, where
           `tag = 0` denotes `Register.temp` (and `val` is unused) and
           `tag = 1` denotes `Register.given val`. -/

private def readU32LE (bs : ByteArray) (off : Nat) : UInt32 :=
  let b0 := (bs.get! off).toUInt32
  let b1 := (bs.get! (off + 1)).toUInt32
  let b2 := (bs.get! (off + 2)).toUInt32
  let b3 := (bs.get! (off + 3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

private def pushU32LE (bs : ByteArray) (x : UInt32) : ByteArray :=
  bs.push (x &&& 0xff).toUInt8
    |>.push ((x >>> 8) &&& 0xff).toUInt8
    |>.push ((x >>> 16) &&& 0xff).toUInt8
    |>.push ((x >>> 24) &&& 0xff).toUInt8

private def encodeRegister : Register → UInt32 × UInt32
  | .temp    => (0, 0)
  | .given r => (1, r)

/-- Decode a packed byte input, run the algorithm, and pack the output. -/
@[export rust_seq_parallel_copies]
def rustSeqParallelCopies (input : @& ByteArray) : ByteArray := Id.run do
  let n := input.size / 8
  let mut pairs : Array (UInt32 × UInt32) := Array.mkEmpty n
  for i in [:n] do
    let off := i * 8
    pairs := pairs.push (readU32LE input off, readU32LE input (off + 4))
  let result := sequenceParallelCopies pairs
  let mut out : ByteArray := ByteArray.empty
  for (a, b) in result do
    let (ta, va) := encodeRegister a
    let (tb, vb) := encodeRegister b
    out := pushU32LE out ta
    out := pushU32LE out va
    out := pushU32LE out tb
    out := pushU32LE out vb
  return out

end ParallelCopies
