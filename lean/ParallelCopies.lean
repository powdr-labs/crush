import Std.Data.HashMap

/-!
# Parallel-Copy Sequencing

A port of `crush::loader::rwm::flattening::sequence_parallel_copies` to Lean 4.

Given a set of *parallel* assignments `dst_i := src_i` with a unique destination
for each pair, produce a sequential schedule of register copies with at most one
extra temporary register that has the same post-state as the parallel assignment.

The algorithm has two phases:

* **Phase 1 — prune trees.** A "leaf" is a register that is a destination
  but not itself a source. Emit `(src[leaf], leaf)`, then update the graph
  by *source-swapping*: the leaf takes over its source's remaining out-edges.
  This naturally severs any cycle that has a tree hanging off it, so after
  phase 1 only pure cycles remain.

* **Phase 2 — break remaining cycles.** Save the cycle's start register into
  a single temporary, walk the cycle emitting intra-cycle copies, then close
  it with `temp → last`. The temporary is reused as the destination of the
  first non-cycle copy when one exists, otherwise a fresh `Register.temp`.

Phase-2 copies are emitted *first* in the final sequence so the temporary
register isn't overwritten before it's needed.
-/

namespace ParallelCopies

/-- An output register: either the dedicated temporary used to break cycles,
    or one of the original registers carried over from the input. -/
inductive Register
  | temp
  | given (r : UInt32)
  deriving Repr, BEq, Hashable, Inhabited

/-! ## Graph representation -/

/-- Adjacency record for a register node: its (unique) source, if any, and
    the registers it is copied into. -/
private structure RegConn where
  src  : Option UInt32 := none
  dest : Array UInt32  := #[]
  deriving Inhabited

private abbrev Graph := Std.HashMap UInt32 RegConn

/-- Functional `g[k] ← f (g[k] ?? {})`. Inserting a default before the update
    lets us treat the graph as a total function from registers to `RegConn`s. -/
private def upsert (g : Graph) (k : UInt32) (f : RegConn → RegConn) : Graph :=
  g.insert k (f (g.getD k {}))

/-! ## Phase 0 — graph construction -/

/-- Fold one `(src, dst)` pair into the graph, enforcing the pre-condition
    that every destination has at most one source. Self-copies and exact
    duplicates are silently dropped. -/
private def addEdge (g : Graph) : UInt32 × UInt32 → Graph
  | (src, dst) =>
    if src == dst then g
    else match (g.getD dst {}).src with
      | some s =>
        if s == src then g
        else panic! s!"Pre-condition violated: destination register {dst} is written to more than once"
      | none =>
        g |> (upsert · dst fun e => { e with src := some src })
          |> (upsert · src fun e => { e with dest := e.dest.push dst })

private def buildGraph (pairs : Array (UInt32 × UInt32)) : Graph :=
  pairs.foldl addEdge ∅

/-! ## Phase 1 — prune trees -/

/-- All registers that are destinations but have no outgoing edges. -/
private def leavesOf (g : Graph) : Array UInt32 :=
  g.fold (init := #[]) fun acc reg c =>
    if c.dest.isEmpty && c.src.isSome then acc.push reg else acc

/-- Source-swap step: the value originally at the source now lives at
    `target`, so every register in `remaining` (the source's other out-edges)
    is rewired to read from `target` instead. -/
private def sourceSwap (target : UInt32) (remaining : Array UInt32)
    (g : Graph) : Graph :=
  let g := remaining.foldl (init := g) fun g d =>
    upsert g d fun e => { e with src := some target }
  g.insert target { src := none, dest := remaining }

/-- Process one leaf: emit `(source, target)`, prune the edge, and apply the
    source-swap. Returns the new graph, the (possibly enlarged) leaves queue,
    and the emitted copy. -/
private def peelLeaf (target : UInt32) (g : Graph) (leaves : Array UInt32)
    : Graph × Array UInt32 × (UInt32 × UInt32) :=
  let source   := (g.get! target).src.get!
  let srcN     := g.get! source
  let remaining := srcN.dest.filter (· != target)
  -- Detach `source` from its old out-edges; if it has no source itself it
  -- can leave the graph entirely, otherwise it becomes a new leaf.
  let (g, leaves) :=
    if srcN.src.isNone then
      (g.erase source, leaves)
    else
      (g.insert source { srcN with dest := #[] }, leaves.push source)
  -- Rewire the remaining out-edges through `target`.
  let g :=
    if remaining.isEmpty then g.erase target
    else sourceSwap target remaining g
  (g, leaves, (source, target))

/-- Phase 1 driver: peel leaves until none remain. The leftover graph
    contains only pure cycles. -/
private partial def pruneTrees
    (g : Graph) (leaves : Array UInt32) (acc : Array (UInt32 × UInt32))
    : Graph × Array (UInt32 × UInt32) :=
  match leaves.back? with
  | none => (g, acc)
  | some target =>
    let (g, leaves, copy) := peelLeaf target g leaves.pop
    pruneTrees g leaves (acc.push copy)

/-! ## Phase 2 — break remaining cycles -/

/-- The minimum key of a non-empty graph. `Std.HashMap` iteration order is
    unspecified, so we scan keys ourselves to keep output deterministic. -/
private def smallestKey? (g : Graph) : Option UInt32 :=
  g.fold (init := none) fun best k _ =>
    some <| best.elim k (Nat.min k.toNat ·.toNat |>.toUInt32)

/-- Walk one cycle, removing each visited node and emitting copies. Returns
    the *last* visited register — its content will be filled in from the
    temporary register that holds the cycle's original starting value. -/
private partial def walkCycle
    (start curr : UInt32) (g : Graph) (acc : Array (Register × Register))
    : UInt32 × Graph × Array (Register × Register) :=
  let source := (g.get! curr).src.get!
  let g := g.erase curr
  if source == start then
    (curr, g, acc)
  else
    walkCycle start source g (acc.push (.given source, .given curr))

/-- Break a single cycle: spill the start into `tmp`, walk the cycle, then
    fill the last register from `tmp`. -/
private def breakOneCycle
    (tmp : Register) (start : UInt32)
    (g : Graph) (acc : Array (Register × Register))
    : Graph × Array (Register × Register) :=
  let (last, g, acc) := walkCycle start start g (acc.push (.given start, tmp))
  (g, acc.push (tmp, .given last))

/-- Phase 2 driver: drain every remaining cycle. -/
private partial def breakCycles
    (tmp : Register) (g : Graph) (acc : Array (Register × Register))
    : Array (Register × Register) :=
  match smallestKey? g with
  | none       => acc
  | some start => let (g, acc) := breakOneCycle tmp start g acc; breakCycles tmp g acc

/-! ## Top-level entry point -/

/-- Sequence a set of parallel copies into a list of sequential copies that
    preserves the parallel-assignment semantics, using at most one temporary.

    **Pre-condition**: every destination register appears at most once. -/
def sequenceParallelCopies
    (pairs : Array (UInt32 × UInt32)) : Array (Register × Register) :=
  let g                := buildGraph pairs
  let (g, nonCycle)    := pruneTrees g (leavesOf g) #[]
  -- Reuse the first non-cycle destination as the cycle-breaking temp when we
  -- have one — its prior value has already been copied out.
  let tmp : Register   := nonCycle[0]?.elim .temp (fun (_, d) => .given d)
  breakCycles tmp g #[] ++ nonCycle.map fun (s, d) => (.given s, .given d)

/-! ## FFI surface

The C bridge passes packed little-endian byte streams across the boundary:

* Input  : `[src₀, dst₀, src₁, dst₁, …]` — `UInt32` pairs.
* Output : `[tag_s, val_s, tag_d, val_d, …]` per emitted copy.
  `tag = 0` means `Register.temp` (and `val` is unused); `tag = 1` means
  `Register.given val`.
-/

private def readU32LE (bs : ByteArray) (off : Nat) : UInt32 :=
  let byte (i : Nat) : UInt32 := (bs.get! (off + i)).toUInt32
  byte 0 ||| (byte 1 <<< 8) ||| (byte 2 <<< 16) ||| (byte 3 <<< 24)

private def pushU32LE (bs : ByteArray) (x : UInt32) : ByteArray :=
  [0, 8, 16, 24].foldl (init := bs) fun bs shift =>
    bs.push ((x >>> shift.toUInt32) &&& 0xff).toUInt8

private def encodeRegister : Register → UInt32 × UInt32
  | .temp    => (0, 0)
  | .given r => (1, r)

private def decodePairs (bytes : ByteArray) : Array (UInt32 × UInt32) :=
  let n := bytes.size / 8
  (Array.range n).map fun i =>
    let off := i * 8
    (readU32LE bytes off, readU32LE bytes (off + 4))

private def encodeCopies (copies : Array (Register × Register)) : ByteArray :=
  copies.foldl (init := ByteArray.empty) fun bs (a, b) =>
    let (ta, va) := encodeRegister a
    let (tb, vb) := encodeRegister b
    [ta, va, tb, vb].foldl pushU32LE bs

@[export rust_seq_parallel_copies]
def rustSeqParallelCopies (input : @& ByteArray) : ByteArray :=
  encodeCopies (sequenceParallelCopies (decodePairs input))

end ParallelCopies
