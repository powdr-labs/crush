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
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

/-! ## Graph representation -/

/-- Adjacency record for a register node: its (unique) source, if any, and
    the registers it is copied into. -/
structure RegConn where
  src  : Option UInt32 := none
  dest : Array UInt32  := #[]
  deriving Inhabited

abbrev Graph := Std.HashMap UInt32 RegConn

/-- Functional `g[k] ← f (g[k] ?? {})`. Inserting a default before the update
    lets us treat the graph as a total function from registers to `RegConn`s. -/
def upsert (g : Graph) (k : UInt32) (f : RegConn → RegConn) : Graph :=
  g.insert k (f (g.getD k {}))

/-! ## Phase 0 — graph construction -/

/-- Fold one `(src, dst)` pair into the graph, enforcing the pre-condition
    that every destination has at most one source. Self-copies and exact
    duplicates are silently dropped. -/
def addEdge (g : Graph) : UInt32 × UInt32 → Graph
  | (src, dst) =>
    if src == dst then g
    else match (g.getD dst {}).src with
      | some s =>
        if s == src then g
        else panic! s!"Pre-condition violated: destination register {dst} is written to more than once"
      | none =>
        g |> (upsert · dst fun e => { e with src := some src })
          |> (upsert · src fun e => { e with dest := e.dest.push dst })

def buildGraph (pairs : Array (UInt32 × UInt32)) : Graph :=
  pairs.foldl addEdge ∅

/-! ## Phase 1 — prune trees -/

/-- All registers that are destinations but have no outgoing edges. -/
def leavesOf (g : Graph) : Array UInt32 :=
  g.fold (init := #[]) fun acc reg c =>
    if c.dest.isEmpty && c.src.isSome then acc.push reg else acc

/-- Source-swap step: the value originally at the source now lives at
    `target`, so every register in `remaining` (the source's other out-edges)
    is rewired to read from `target` instead. -/
def sourceSwap (target : UInt32) (remaining : Array UInt32)
    (g : Graph) : Graph :=
  let g := remaining.foldl (init := g) fun g d =>
    upsert g d fun e => { e with src := some target }
  g.insert target { src := none, dest := remaining }

/-- Process one leaf: emit `(source, target)`, prune the edge, and apply the
    source-swap. Returns the new graph, the (possibly enlarged) leaves queue,
    and the emitted copy. -/
def peelLeaf (target : UInt32) (g : Graph) (leaves : Array UInt32)
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
    contains only pure cycles. Recursion is structurally bounded by
    `fuel`; in `sequenceParallelCopies` we always pass a `fuel` that is
    large enough (the number of input pairs is an upper bound on the
    number of edges, hence on the number of iterations). -/
def pruneTrees
    (fuel : Nat)
    (g : Graph) (leaves : Array UInt32) (acc : Array (UInt32 × UInt32))
    : Graph × Array (UInt32 × UInt32) :=
  match fuel, leaves.back? with
  | 0,    _      => (g, acc)
  | _,    none   => (g, acc)
  | n+1,  some target =>
    let (g, leaves, copy) := peelLeaf target g leaves.pop
    pruneTrees n g leaves (acc.push copy)

/-! ## Phase 2 — break remaining cycles -/

/-- The minimum key of a non-empty graph. `Std.HashMap` iteration order is
    unspecified, so we scan keys ourselves to keep output deterministic. -/
def smallestKey? (g : Graph) : Option UInt32 :=
  g.fold (init := none) fun best k _ =>
    some <| best.elim k (Nat.min k.toNat ·.toNat |>.toUInt32)

/-- Walk one cycle, removing each visited node and emitting copies. Returns
    the *last* visited register — its content will be filled in from the
    temporary register that holds the cycle's original starting value.
    `fuel` strictly bounds the walk; the cycle's length is an upper bound. -/
def walkCycle
    (fuel : Nat) (start curr : UInt32)
    (g : Graph) (acc : Array (Register × Register))
    : UInt32 × Graph × Array (Register × Register) :=
  match fuel with
  | 0     => (curr, g, acc)
  | n+1   =>
    let source := (g.get! curr).src.get!
    let g := g.erase curr
    if source == start then
      (curr, g, acc)
    else
      walkCycle n start source g (acc.push (.given source, .given curr))

/-- Break a single cycle: spill the start into `tmp`, walk the cycle, then
    fill the last register from `tmp`. -/
def breakOneCycle
    (fuel : Nat) (tmp : Register) (start : UInt32)
    (g : Graph) (acc : Array (Register × Register))
    : Graph × Array (Register × Register) :=
  let (last, g, acc) := walkCycle fuel start start g (acc.push (.given start, tmp))
  (g, acc.push (tmp, .given last))

/-- Phase 2 driver: drain every remaining cycle. Outer fuel bounds the
    number of distinct cycles; inner fuel (passed to `breakOneCycle`)
    bounds each cycle's length. -/
def breakCycles
    (fuel : Nat) (tmp : Register) (g : Graph)
    (acc : Array (Register × Register))
    : Array (Register × Register) :=
  match fuel, smallestKey? g with
  | 0,   _          => acc
  | _,   none       => acc
  | n+1, some start =>
    let (g, acc) := breakOneCycle fuel tmp start g acc
    breakCycles n tmp g acc

/-! ## Top-level entry point -/

/-- Sequence a set of parallel copies into a list of sequential copies that
    preserves the parallel-assignment semantics, using at most one temporary.

    **Pre-condition**: every destination register appears at most once.

    Fuel choice: `pairs.size + 1` is a safe upper bound on every loop's
    iteration count.  Phase 1 removes one edge per step, and the graph has at
    most `pairs.size` edges.  Phase 2 visits at most `pairs.size` nodes total
    across all cycles (each erase strictly decreases `g.size`). -/
def sequenceParallelCopies
    (pairs : Array (UInt32 × UInt32)) : Array (Register × Register) :=
  let fuel             := pairs.size + 1
  let g                := buildGraph pairs
  let (g, nonCycle)    := pruneTrees fuel g (leavesOf g) #[]
  -- Reuse the first non-cycle destination as the cycle-breaking temp when we
  -- have one — its prior value has already been copied out.
  let tmp : Register   := nonCycle[0]?.elim .temp (fun (_, d) => .given d)
  breakCycles fuel tmp g #[] ++ nonCycle.map fun (s, d) => (.given s, .given d)

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

def decodePairs (bytes : ByteArray) : Array (UInt32 × UInt32) :=
  let n := bytes.size / 8
  (Array.range n).map fun i =>
    let off := i * 8
    (readU32LE bytes off, readU32LE bytes (off + 4))

def encodeCopies (copies : Array (Register × Register)) : ByteArray :=
  copies.foldl (init := ByteArray.empty) fun bs (a, b) =>
    let (ta, va) := encodeRegister a
    let (tb, vb) := encodeRegister b
    [ta, va, tb, vb].foldl pushU32LE bs

@[export rust_seq_parallel_copies]
def rustSeqParallelCopies (input : @& ByteArray) : ByteArray :=
  encodeCopies (sequenceParallelCopies (decodePairs input))

end ParallelCopies
