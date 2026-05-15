# `lean/` — formally verified parallel-copy sequencing

This directory contains a Lean 4 reimplementation of `crush::loader::rwm::flattening::sequence_parallel_copies`, together with a full machine-checked correctness proof. The Rust side calls into Lean across a small C FFI bridge (`c/ffi.c`); the entry from Rust is `src/loader/rwm/flattening/sequence_parallel_copies.rs`.

The compiled artefacts are linked statically into the `crush` binary, so a user of the compiler never has to install Lean.

## What the module does

A *parallel-copy block* is a set of register assignments `{ dst_i := src_i }` that should all read their sources from the *same* pre-state — semantically simultaneous. A processor with only sequential moves cannot do this directly: writing `b := a` then `c := b` would have `c` read the new `b`, not the original.

Given such a parallel block, the algorithm produces a sequence of one-at-a-time copies that, when executed left to right, leaves every destination holding the value the parallel spec requires. At most one extra register (the *temp*) is needed, and only when the input contains a true cycle (e.g. `a := b; b := a`).

The Rust call site needs this in register allocation: when fanning values into the locations the next basic block expects them, those locations may overlap with their own sources, and we need a sound serialisation.

## Files

| File                              | Role                                                                            |
| --------------------------------- | ------------------------------------------------------------------------------- |
| `ParallelCopies.lean`             | Algorithm + FFI surface (`@[export rust_seq_parallel_copies]`)                  |
| `ParallelCopies/Spec.lean`        | Mathematical spec: `applyParallel`, `applySequential`, `RealisesParallel`       |
| `ParallelCopies/SpecLemmas.lean`  | Algebraic identities about the spec (used everywhere downstream)                |
| `ParallelCopies/ListSpec.lean`    | `List`-based mirror of the spec, with `Array ↔ List` bridge lemmas              |
| `ParallelCopies/Phase1.lean`      | Tree-pruning soundness (`peelStep_sound`, `phase1_sound`)                       |
| `ParallelCopies/Phase2.lean`      | Cycle-breaking soundness + preprocess lemmas                                    |
| `ParallelCopies/Proofs.lean`      | Assembly: phase 1 + phase 2 + preprocess → `sequenceParallelCopies_correct`     |
| `c/ffi.c`                         | Lean ↔ Rust bridge: marshals a flat `u32` byte stream both ways                 |
| `lakefile.toml`, `lean-toolchain` | Lake build config                                                               |

## API entry points

### Lean → Rust (the live interface)

* `ParallelCopies.rustSeqParallelCopies : @& ByteArray → ByteArray` — `@[export rust_seq_parallel_copies]`.
  Decodes a packed little-endian `[src₀, dst₀, src₁, dst₁, …]` byte stream, runs the algorithm, returns a packed `[tag_s, val_s, tag_d, val_d, …]` byte stream where `tag = 0` means `Register.temp` and `tag = 1` means `Register.given val`. This is what `src/loader/rwm/flattening/sequence_parallel_copies.rs` calls.

### Pure Lean (used by the proofs and tests)

* `ParallelCopies.sequenceParallelCopies : Array Edge → Array (Register × Register)` — array-typed wrapper matching the FFI shape.
* `ParallelCopies.sequenceParallelCopiesL : List Edge → List (Register × Register)` — the list-typed underlying implementation; everything in the proof world lives here.

### Spec surface

* `Spec.applyParallel : Array Edge → State → State` — what the answer **should** be.
* `Spec.applySequential : Array (Register × Register) → SState → SState` — what running the algorithm's output **actually does**.
* `Spec.RealisesParallel impl : Prop` — the correctness predicate, satisfied by `sequenceParallelCopies` (theorem `sequenceParallelCopies_correct`).

## What we're proving

The single top-level theorem (`Proofs.lean`):

```lean
theorem sequenceParallelCopies_correct :
    RealisesParallel sequenceParallelCopies
```

Unfolded, this says: **for every** well-formed input `pairs` and **every** initial state `s` and **every** concrete register `r`,

```
applySequential (sequenceParallelCopies pairs) (lift s) (.given r)
  = applyParallel pairs s r
```

The well-formed-ness premise (`WellFormed pairs`) is the same contract the Rust shim validates: each non-self-copy destination is written by at most one distinct source. Self-copies and exact-duplicate edges are allowed (the algorithm filters them).

Axioms used: exactly Lean's three foundational ones — `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `nativeDecide`, no native-code escape hatches. (`#print axioms ParallelCopies.sequenceParallelCopies_correct` reports this.)

## The spec, made precise

### State

* `State := UInt32 → UInt32` — the world the parallel block sees.
* `SState := Register → UInt32` — the world the sequential interpreter sees, with one extra `.temp` slot tracking the cycle-breaking register.
* `lift : State → SState` — embeds a concrete state, putting any value in `.temp` (its initial contents are irrelevant; the algorithm always writes `.temp` before reading it).

### Parallel semantics — `applyParallel`

`applyParallel pairs s` returns a new state where, at register `r`:

* if some `(src, r)` is in `pairs` with `src ≠ r`, the new value is `s src`;
* otherwise the value is `s r`, unchanged.

Reads are all from `s`, not from intermediate values, so the result is independent of the order pairs appear in. Self-copies and exact duplicates are no-ops by the `src ≠ dst` guard in `Pair.appliesTo` (and the well-formed contract makes the writer for `r` unique when one exists).

### Sequential semantics — `applySequential`

A left-fold of `step : SState → (Register × Register) → SState`, where `step σ (src, dst)` updates only `dst` to `σ src`. The algorithm's output is an `Array (Register × Register)` and `applySequential` is `Array.foldl step`.

### The promise — `RealisesParallel`

Equality of the two semantics **on every concrete register**. We deliberately say nothing about `.temp`'s final contents — it is implementation scratch.

## The algorithm in three pieces

```
sequenceParallelCopiesL pairs =
    let es              = preprocess pairs                  -- phase 0
    let (es, nonCycle)  = phase1 fuel es []                  -- phase 1
    nonCycle.map (·,·)
      ++ phase2 fuel Register.temp es []                     -- phase 2
```

Phase 0 normalises (drops self-copies and exact duplicates). Phase 1 prunes everything except pure cycles, using a *source-swap* trick. Phase 2 breaks each remaining cycle with one save-to-temp + walk + restore-from-temp.

The schedule order is `nonCycle ++ phase2`. At the Lean spec level this is sound because `.temp` and `.given _` are disjoint ADT variants, so the two blocks act on disjoint registers and any ordering is equivalent. (The Rust consumer, when it materialises `.temp` to a concrete register, has to take care that the materialised temp doesn't alias a `nonCycle` destination; see the comment in `ParallelCopies.lean` and `src/loader/rwm/flattening/mod.rs::parallel_copy`.)

## The proof skeleton, and why each piece is needed

The proof is structured so that each module proves *one* property about *one* phase, and `Proofs.lean` chains them.

### Phase 0 — `preprocess` (preserves the parallel spec)

What we prove (in `Phase2.lean`, despite the name — that's where the preprocess lemmas live):

* `preprocess_uniqueDst`, `preprocess_no_self`, `preprocess_dsts_nodup` — structural invariants needed by phases 1 and 2.
* `applyParallelLS_preprocess_eq` — `applyParallelLS (preprocess pairs) σ = applyParallelLS pairs σ` on `.given r`.

**Why needed.** Phase 1 starts from `preprocess pairs`, not from `pairs`. Without this we cannot connect the algorithm's output back to the user-facing `applyParallel pairs`.

**Why it holds.** A self-copy `(r, r)` never `appliesTo` any register, and an exact duplicate `(s, d)` is found by `find?` exactly when the first copy of it is. So `findWriter?` returns identical answers before and after preprocessing.

**Why sufficient.** It gives us a `pairs.toList → preprocess pairs.toList` rewrite at the very top of the final proof, after which everything is about the well-behaved list.

### Phase 1 — tree pruning with source-swap

The key fact (`Phase1.lean`):

```
phase1_sound :
  applyParallelLS original σ
    = applyParallelLS es' (applySequentialL (acc'.map edgeToCopy) σ)
```

where `(es', acc') = phase1 fuel es acc` and the hypothesis is the same equation holding at the start of the call.

**Why needed.** Phase 1 emits a list of *sequential* copies, but the rest of the proof needs to reason about what the parallel block on the *residual* `es'` does on top of those sequential writes. This lemma is exactly that bridge.

**Why it holds.** Each loop iteration peels a leaf `(s, d)` via `peelStep s d es`, which (i) drops that edge and (ii) rewires any remaining edge whose source is `s` to read from `d` instead. The local soundness lemma `peelStep_sound` shows that emitting the sequential copy `(.given s, .given d)` and then taking the parallel block of the rewired graph reads the same values at every register as the parallel block of the original — case-split on whether the register is `d`, some other written register, or untouched. The induction over `phase1` just chains this single-step lemma.

The source-swap is the whole game: it ensures that subsequent copies that *would* have read from `s` now read from `d`, which already holds `s`'s pre-block value. After phase 1, only pure cycles remain in `es'`.

**Why sufficient.** Combined with the structural preservation lemmas (`phase1_preserves_uniqueDst`, `phase1_preserves_no_self`, `phase1_residual_allOnCycle`), it leaves phase 2 with a graph that consists of disjoint cycles only — the exact precondition phase 2 needs.

### Phase 2 — cycle breaking

The key fact (`Phase2.lean`):

```
phase2_sound :
  applySequentialL (phase2 fuel .temp es acc) σ (.given r)
    = applyParallelLS es (applySequentialL acc σ) (.given r)
```

under `UniqueDst es`, no self-loops, `AllOnCycle es`, and enough fuel.

**Why needed.** Phase 2 produces the cycle-breaking schedule. We need to show that, applied to the state already updated by phase 1's sequential copies, it leaves every cycle node holding the value the parallel block would have placed there.

**Why it holds.**

* For a *single* cycle (`breakOneCycle_sound_at_cycle`), the schedule is: save the cycle's start into `.temp`, walk the cycle emitting `(.given src, .given curr)` in reverse, then restore the last register from `.temp`. The save-then-restore makes the cycle behave just like a parallel rotation. The walk visits each cycle node exactly once (`walkVisits_eq_of_onCycle`, `walkVisits_nodup_of_onCycle`), so no copy clobbers a not-yet-read register.
* For *all* remaining cycles (`phase2_sound` itself), we induct on `fuel`. Each step picks the smallest destination still in `es`, handles its cycle, and recurses on the residual. The non-trivial part is showing that after breaking one cycle the residual still has `AllOnCycle` (`allOnCycle_preserved_by_breakOneCycle`): the writer chain of any remaining destination is fully disjoint from the cycle we just removed, by `cycle_disjoint_of_start_not_in`.
* The temp register is touched only in two designated copies per cycle (write then read), and `AllOnCycle` plus `UniqueDst` together imply that across cycles the temp is fully written before it is read again, so distinct cycles cannot interfere through `.temp`.

**Why sufficient.** It exactly produces the equation we need to chain with `phase1_sound` in the assembly step.

### Spec algebra

`SpecLemmas.lean` and `ListSpec.lean` collect basic identities — `applyParallel_nil`, `step_dst`, `applySequential_append`, `lift_given`, `applySequentialL_append`, etc. — plus the `Array ↔ List` bridges (`applySequential_eq_L`, `applyParallel_eq_L`).

**Why needed.** The algorithm and the proofs work with `List`, but the FFI signature is `Array`. The bridge lemmas let the final theorem be stated in array terms while every algorithmic step is reasoned about in list terms (where induction is uniform).

**Why sufficient.** They are pure desugaring / `foldl_append` identities, but without them the array/list mismatch would require ad-hoc juggling at every step.

## Trust boundary — what's verified vs what's trusted

The theorem above is a statement about the **abstract schedule**: a list of `(Register, Register)` copies where `Register = .temp | .given UInt32`. Lean treats `.temp` and every `.given r` as disjoint registers *by ADT construction* — they cannot alias.

When the schedule is executed by `crush` it has to be lowered to concrete machine moves over `u32` register slots. That step happens in Rust, in `src/loader/rwm/flattening/mod.rs::parallel_copy`, and is **outside** the Lean theorem:

* The Rust shim collects every `.given r` appearing as a source or destination in the schedule (the *participant set*).
* When the materialiser is asked to assign a concrete `u32` to `.temp`, it calls `Context::allocate_tmp_type` and retries until the result is not in the participant set.

This is the right thing to do, but it is **trusted code**: if the participant collection were wrong, or if `allocate_tmp_type` returned a register that was live-and-still-needed in the surrounding compiler state, the verified Lean theorem would not catch it. The earlier bug where wasm-pipeline tests broke was exactly an instance of this — a materialised `.temp` aliasing a parallel-copy destination — and it was found by integration tests, not by Lean.

If you change `parallel_copy`, `allocate_tmp_type`, or the way the participant set is collected, treat those changes as touching the trust boundary and validate them with full pipeline tests.

A future, stronger version of this module could move temp materialisation into the verified algorithm (port the original Rust optimisation of using the first non-cycle destination as the temp), at which point the output type becomes `u32` and the trust boundary collapses. The current code does not do that.

## How they combine in `Proofs.lean`

The final theorem proof is a single chain of rewrites:

1. Translate the statement from `Array.applyParallel / applySequential` to the `List` mirror via `applyParallel_eq_L` and `applySequential_eq_L`.
2. Unfold `sequenceParallelCopiesL` to expose `nonCycle.map ec ++ phase2 …`.
3. Decompose the sequential application with `applySequentialL_append`.
4. Rewrite the phase-2 piece with `phase2_sound` (with `acc = []`) to get `applyParallelLS es_residual (applySequentialL (nC.map ec) σ)`.
5. Rewrite that with `phase1_sound` to get `applyParallelLS (preprocess pairs) σ`.
6. Rewrite that with `applyParallelLS_preprocess_eq` to get `applyParallelLS pairs σ`.
7. Conclude — `applyParallelLS pairs σ (.given r) = applyParallel pairs s r` by definition of `lift`.

Each rewrite is justified by exactly one lemma above. None of them is circular, and the only structural premises (`UniqueDst`, no self-loops, `AllOnCycle` for `es_residual`) are supplied by the preservation lemmas across phases 0 and 1.

## Building and checking

```bash
cd lean
lake build                         # checks every proof
```

To re-check the axiom dependencies of the top theorem (no `sorry`, no `nativeDecide`, no compiler trust):

```lean
import ParallelCopies.Proofs
#print axioms ParallelCopies.sequenceParallelCopies_correct
-- → [propext, Classical.choice, Quot.sound]
```

The `cargo build` of `crush` invokes `lake build` automatically and links the resulting static library, so consumers of the Rust crate get the verified implementation transparently.
