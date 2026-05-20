//! Differential and property tests that exercise both the current Lean-
//! backed `sequence_parallel_copies` and the pre-port Rust implementation
//! kept in [`legacy_reference`].
//!
//! Three buckets:
//!
//! * **Regression sweep** — runs the existing 47 unit-test inputs through
//!   the *legacy* impl, asserting it realises parallel semantics. This is a
//!   sanity baseline; if it ever fails, the legacy impl had a latent bug.
//!
//! * **Property sweep** — generates random well-formed inputs from a seeded
//!   PRNG and checks that *both* implementations produce schedules that
//!   realise the parallel-copy spec. Any failure either pins a bug in one
//!   of the implementations, or a misunderstanding of the contract.
//!
//! * **Targeted corners** — explicit test cases for the load-bearing
//!   patterns the Lean proof had to handle (multi-cycle temp reuse,
//!   `nC.first.dst` aliasing a cycle node, deep mixed self-copy/duplicate
//!   interleaves, etc.).
//!
//! The oracle (`realises_parallel`) is a direct Rust transcription of the
//! Lean spec `Spec.RealisesParallel`: it applies the emitted schedule
//! sequentially with `Register::Temp` modelled as a slot disjoint from
//! every concrete register, and checks every parallel destination ends up
//! holding the value the naive parallel block would have written.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::legacy_reference::sequence_parallel_copies_legacy;
use super::sequence_parallel_copies::{Register, sequence_parallel_copies as new_spc};

// -----------------------------------------------------------------------
// Oracle: the Lean spec, transcribed to Rust.
// -----------------------------------------------------------------------

/// Apply the parallel-copy block in the obvious naive way: read every
/// non-self source from the original state, then write each destination.
/// In presence of duplicates with the same source, behaviour matches the
/// `find?`/"first-writer" semantics of `Spec.applyParallel`.
fn apply_parallel(pairs: &[(u32, u32)], initial: &HashMap<u32, u32>) -> HashMap<u32, u32> {
    let read = |state: &HashMap<u32, u32>, r: u32| *state.get(&r).unwrap_or(&r);

    // First-writer-wins: walk pairs in order and only honour the first
    // non-self write per destination. This matches `Spec.findWriter?`
    // which does `pairs.find?` and stops at the first match.
    let mut writer_for: BTreeMap<u32, u32> = BTreeMap::new();
    for &(s, d) in pairs {
        if s == d {
            continue;
        }
        writer_for.entry(d).or_insert(s);
    }

    let mut out = initial.clone();
    for (d, s) in writer_for {
        out.insert(d, read(initial, s));
    }
    out
}

/// Apply a sequential schedule with `Register::Temp` as a sentinel slot
/// disjoint from every concrete register.
fn apply_sequential(
    schedule: &[(Register, Register)],
    initial: &HashMap<u32, u32>,
) -> HashMap<u32, u32> {
    // Use a value distinct from any plausible u32 register index for the
    // temp slot key. We keep it as a special-cased HashMap entry.
    const TEMP_KEY: u32 = u32::MAX;
    let mut state = initial.clone();
    // Initialise temp with a sentinel that's distinct from any register's
    // initial-value pattern used by the property test (which uses values
    // ≤ u32::MAX / 2).
    state.insert(TEMP_KEY, 0xDEAD_BEEF);

    let read = |state: &HashMap<u32, u32>, r: Register| match r {
        Register::Given(r) => *state.get(&r).unwrap_or(&r),
        Register::Temp => *state.get(&TEMP_KEY).unwrap(),
    };
    for &(s, d) in schedule {
        let v = read(&state, s);
        match d {
            Register::Given(r) => {
                state.insert(r, v);
            }
            Register::Temp => {
                state.insert(TEMP_KEY, v);
            }
        }
    }
    state.remove(&TEMP_KEY);
    state
}

/// The Lean spec, end-to-end: applying the schedule sequentially must
/// give the same per-concrete-register state as applying the parallel
/// block. Returns `Ok(())` or a description of the mismatch.
fn realises_parallel(
    pairs: &[(u32, u32)],
    schedule: &[(Register, Register)],
    initial: &HashMap<u32, u32>,
) -> Result<(), String> {
    let parallel = apply_parallel(pairs, initial);
    let sequential = apply_sequential(schedule, initial);

    // Compare on every register that the parallel block touches plus
    // every source/destination that appears in `pairs` (so we also notice
    // wrongly-clobbered sources).
    let mut interesting: BTreeSet<u32> = BTreeSet::new();
    for &(s, d) in pairs {
        interesting.insert(s);
        interesting.insert(d);
    }

    for &r in &interesting {
        let expected = parallel.get(&r).copied().unwrap_or(r);
        let actual = sequential.get(&r).copied().unwrap_or(r);
        if expected != actual {
            return Err(format!(
                "register {r}: parallel says {expected}, sequential says {actual}\n\
                 pairs    = {pairs:?}\n\
                 schedule = {schedule:?}"
            ));
        }
    }
    Ok(())
}

fn initial_state(pairs: &[(u32, u32)]) -> HashMap<u32, u32> {
    // Initialise every distinct register that appears to a unique value
    // derived from its index. Using `r * 7919 + 11` makes accidental
    // coincidences (e.g. r == r * 7919 + 11) impossible for u32.
    let mut state = HashMap::new();
    for &(s, d) in pairs {
        state.insert(s, s.wrapping_mul(7919).wrapping_add(11));
        state.insert(d, d.wrapping_mul(7919).wrapping_add(11));
    }
    state
}

fn run_through<I, F>(pairs: Vec<(u32, u32)>, impl_fn: F)
where
    F: FnOnce(Vec<(u32, u32)>) -> I,
    I: IntoIterator<Item = (Register, Register)>,
{
    let initial = initial_state(&pairs);
    let schedule: Vec<_> = impl_fn(pairs.clone()).into_iter().collect();
    if let Err(msg) = realises_parallel(&pairs, &schedule, &initial) {
        panic!("schedule does not realise parallel-copy semantics:\n{msg}");
    }
}

// -----------------------------------------------------------------------
// Regression sweep: every input from the existing 47-test suite, run
// through the *legacy* impl. The new impl is already covered by the
// existing tests in `sequence_parallel_copies::tests`.
// -----------------------------------------------------------------------

fn legacy_sweep(inputs: &[Vec<(u32, u32)>]) {
    for pairs in inputs {
        run_through(pairs.clone(), sequence_parallel_copies_legacy);
    }
}

#[test]
fn legacy_passes_regression_suite() {
    // The 47 inputs from `sequence_parallel_copies::tests`, replicated
    // here so a future refactor of the unit tests doesn't lose coverage
    // for the legacy impl. Self-copy-only / panic-only cases are
    // excluded (they're tested separately).
    let inputs: &[Vec<(u32, u32)>] = &[
        vec![],
        vec![(0, 1)],
        vec![(0, 0)],
        vec![(0, 0), (1, 1), (2, 2)],
        vec![(0, 1), (2, 3), (4, 5)],
        vec![(0, 1), (1, 2)],
        vec![(0, 1), (1, 2), (2, 3)],
        (0..9).map(|i| (i, i + 1)).collect(),
        vec![(0, 1), (1, 0)],
        vec![(0, 1), (1, 2), (2, 0)],
        vec![(0, 1), (1, 2), (2, 3), (3, 0)],
        vec![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)],
        vec![(0, 1), (0, 2), (0, 3)],
        vec![(0, 1), (1, 2), (1, 3)],
        vec![(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (3, 6)],
        vec![(0, 1), (1, 0), (1, 2)],
        vec![(0, 1), (1, 0), (0, 2), (1, 3)],
        vec![(0, 1), (1, 0), (1, 2), (2, 3), (3, 4)],
        vec![(0, 1), (1, 0), (2, 3), (3, 2)],
        vec![(0, 1), (1, 0), (2, 3), (3, 4), (4, 2)],
        vec![(0, 1), (0, 1)],
        vec![(0, 1), (1, 2), (3, 4), (5, 6)],
        vec![(0, 1), (1, 0), (2, 3), (3, 4), (5, 6)],
        vec![(2, 3), (1, 2), (0, 1)],
        vec![(0, 100), (100, 200), (200, 50)],
        vec![(5, 50), (50, 100), (100, 5)],
        vec![
            (0, 1),
            (1, 2),
            (2, 0),
            (1, 3),
            (3, 4),
            (3, 5),
            (6, 7),
            (7, 8),
            (9, 10),
        ],
        vec![(0, 0), (1, 2), (2, 2), (3, 4)],
        (0..20).map(|i| (i, (i + 1) % 20)).collect(),
        vec![
            (0, 1),
            (0, 2),
            (0, 3),
            (0, 4),
            (0, 5),
            (0, 6),
            (0, 7),
            (0, 8),
            (0, 9),
        ],
        vec![
            (0, 1),
            (0, 2),
            (0, 3),
            (1, 4),
            (1, 5),
            (2, 6),
            (3, 7),
            (3, 8),
        ],
        vec![(0, 1), (1, 0), (0, 2), (1, 3)],
        vec![(0, 1), (1, 2), (0, 3), (3, 4)],
        vec![(0, 1), (1, 2), (2, 0), (0, 3), (1, 4), (2, 5)],
        vec![(0, 0)],
        (0..50).map(|i| (i * 2, i * 2 + 1)).collect(),
        vec![(0, 2), (2, 4), (4, 6), (1, 3), (3, 5), (5, 7)],
        vec![(4, 3), (3, 2), (2, 1), (1, 0)],
        vec![(0, 1), (1, 2), (4, 3)],
        vec![(0, 5), (1, 6), (2, 7), (3, 8), (4, 9)],
        (1..100).map(|i| (i / 3, i)).collect(),
        {
            let mut v = vec![(0, 1), (1, 0)];
            v.extend(vec![(10, 11), (11, 12), (12, 10)]);
            v.extend(vec![(20, 21), (21, 22), (22, 23), (23, 20)]);
            v.extend(vec![(30, 31), (31, 32), (32, 33), (33, 34), (34, 30)]);
            v
        },
    ];
    legacy_sweep(inputs);
}

// -----------------------------------------------------------------------
// Property sweep: seeded random inputs through both implementations.
// -----------------------------------------------------------------------

/// Deterministic PRNG (SplitMix64). Public so the helpers can read it.
struct SplitMix64(u64);

impl SplitMix64 {
    fn new(seed: u64) -> Self {
        Self(seed)
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn next_in(&mut self, n: u32) -> u32 {
        (self.next_u64() % n as u64) as u32
    }
}

/// Generate a *well-formed* parallel-copy input: each non-self destination
/// is written by exactly one source. Allows self-copies and exact-duplicate
/// edges (those are permitted by the contract).
fn gen_wellformed(rng: &mut SplitMix64, max_regs: u32, num_pairs: u32) -> Vec<(u32, u32)> {
    let mut dst_to_src: BTreeMap<u32, u32> = BTreeMap::new();
    let mut pairs = Vec::with_capacity(num_pairs as usize);
    for _ in 0..num_pairs {
        let s = rng.next_in(max_regs);
        let d = rng.next_in(max_regs);
        if s == d {
            pairs.push((s, d)); // self-copy, allowed
            continue;
        }
        if let Some(&prev_s) = dst_to_src.get(&d) {
            // Existing writer for this dst. Reuse the same source to keep
            // the input well-formed (exact-duplicate edge — also allowed).
            pairs.push((prev_s, d));
        } else {
            dst_to_src.insert(d, s);
            pairs.push((s, d));
        }
    }
    pairs
}

#[test]
fn property_sweep_both_impls() {
    let seeds = [1, 2, 3, 4, 5, 42, 0xCAFE, 0xBEEF, 0x1234_5678, 0xDEAD_BEEF];
    for &seed in &seeds {
        let mut rng = SplitMix64::new(seed);
        // Vary input size and register-space density across the run.
        for trial in 0..200u32 {
            let max_regs = 2 + (trial % 30);
            let num_pairs = 1 + (rng.next_u64() % 40) as u32;
            let pairs = gen_wellformed(&mut rng, max_regs, num_pairs);
            // Run through the *new* (Lean-backed) impl.
            run_through(pairs.clone(), new_spc);
            // Run through the *legacy* impl.
            run_through(pairs.clone(), sequence_parallel_copies_legacy);
        }
    }
}

#[test]
fn property_sweep_large_inputs() {
    // Bigger graphs, fewer trials. Stresses the multi-cycle / deep-tree
    // pathways and any latent quadratic-blowup or invariant drift.
    let mut rng = SplitMix64::new(0xF00D);
    for trial in 0..40u32 {
        let max_regs = 50 + (trial % 50);
        let num_pairs = 80 + (rng.next_u64() % 80) as u32;
        let pairs = gen_wellformed(&mut rng, max_regs, num_pairs);
        run_through(pairs.clone(), new_spc);
        run_through(pairs.clone(), sequence_parallel_copies_legacy);
    }
}

// -----------------------------------------------------------------------
// Targeted corners drawn from the Lean proof structure.
// -----------------------------------------------------------------------

#[test]
fn corner_exact_duplicates_interleaved_with_self_copies() {
    // Preprocess corner: self-copies and exact duplicates should both be
    // silently filtered. Lean's `preprocess` handles this; the legacy
    // impl uses two separate guards (`if src == dst` and `if dst_entry.src
    // == Some(src)`). Make sure both still realise the parallel block.
    let pairs = vec![
        (0, 1),
        (0, 0),
        (0, 1), // exact duplicate, after a self-copy
        (1, 1),
        (2, 3),
        (2, 3), // another exact duplicate
        (3, 3),
        (4, 5),
    ];
    run_through(pairs.clone(), new_spc);
    run_through(pairs, sequence_parallel_copies_legacy);
}

#[test]
fn corner_multiple_trees_off_same_cycle_node() {
    // Several tree leaves hang off node 0 (which is also in a 2-cycle
    // with node 1). The source-swap has to fire several times on the
    // same node — historically a source of off-by-one / double-swap bugs.
    let pairs = vec![
        (0, 1),
        (1, 0),
        (0, 2),
        (0, 3),
        (0, 4),
        (0, 5),
        (1, 6),
        (1, 7),
    ];
    run_through(pairs.clone(), new_spc);
    run_through(pairs, sequence_parallel_copies_legacy);
}

#[test]
fn corner_multiple_cycles_sharing_temp_register() {
    // Three independent cycles in the residual. The legacy impl reuses
    // the same `tmp_register = non_cycle_copies.first().map(|&(_, d)|
    // Given(d))` across all three. Lean's `cycle_disjoint_of_start_not_in`
    // is exactly the invariant that makes this safe — but only as long
    // as that `nC.first.dst` really is disjoint from every cycle.
    let pairs = vec![
        // Tree feeding non-cycle copy at dst 100.
        (200, 100),
        // Three independent cycles.
        (0, 1),
        (1, 0),
        (10, 11),
        (11, 12),
        (12, 10),
        (20, 21),
        (21, 22),
        (22, 23),
        (23, 20),
    ];
    run_through(pairs.clone(), new_spc);
    run_through(pairs, sequence_parallel_copies_legacy);
}

#[test]
fn corner_nc_first_dst_adjacent_to_cycle() {
    // The chosen `tmp_register` is the *first* non-cycle destination in
    // emission order. Construct a graph where that destination is a
    // tree leaf hanging off the cycle, so its source is itself a cycle
    // node. Tests the boundary the source-swap was designed to handle.
    let pairs = vec![
        (0, 2), // tree leaf — 2's source is cycle node 0
        (0, 1),
        (1, 0), // 2-cycle
    ];
    run_through(pairs.clone(), new_spc);
    run_through(pairs, sequence_parallel_copies_legacy);
}

#[test]
fn corner_pure_long_cycle() {
    // Pure cycle of 20 nodes, no trees. Phase 2 has to walk the whole
    // cycle with a single temp; tests `walkVisits_nodup_of_onCycle`.
    let pairs: Vec<_> = (0..20).map(|i| (i, (i + 1) % 20)).collect();
    run_through(pairs.clone(), new_spc);
    run_through(pairs, sequence_parallel_copies_legacy);
}

#[test]
fn corner_chain_then_cycle_writing_to_chain_head() {
    // The original source of the chain is also a destination written by
    // the cycle. After source-swap the chain's sources have to be
    // rewritten so they don't read from the cycle's already-modified
    // values.
    let pairs = vec![
        // Cycle.
        (0, 1),
        (1, 0),
        // Chain off cycle node 1: 1 -> 2 -> 3 -> 4.
        (1, 2),
        (2, 3),
        (3, 4),
    ];
    run_through(pairs.clone(), new_spc);
    run_through(pairs, sequence_parallel_copies_legacy);
}

#[test]
fn corner_two_cycles_one_with_attached_tree() {
    // Cycle A is pure; cycle B has a tree hanging off it. Phase 1
    // dissolves cycle B but leaves cycle A intact. Phase 2 then runs
    // exactly one breakOneCycle.
    let pairs = vec![
        // Pure cycle A: 0 <-> 1.
        (0, 1),
        (1, 0),
        // Cycle B with tree: 10 -> 11 -> 10 plus 10 -> 12.
        (10, 11),
        (11, 10),
        (10, 12),
    ];
    run_through(pairs.clone(), new_spc);
    run_through(pairs, sequence_parallel_copies_legacy);
}

#[test]
fn corner_self_loop_at_every_node() {
    // Every input pair is a self-copy. After preprocess the graph is
    // empty. Both impls must produce no copies.
    let pairs: Vec<_> = (0..20).map(|i| (i, i)).collect();
    let new_out: Vec<_> = new_spc(pairs.clone()).collect();
    let legacy_out: Vec<_> = sequence_parallel_copies_legacy(pairs.clone()).collect();
    assert!(
        new_out.is_empty(),
        "new impl emitted copies for all-self-copy input: {:?}",
        new_out
    );
    assert!(
        legacy_out.is_empty(),
        "legacy impl emitted copies for all-self-copy input: {:?}",
        legacy_out
    );
}

#[test]
fn corner_scattered_register_indices() {
    // Register indices spread across the u32 space. Checks that no
    // implementation accidentally allocates space linear in max index.
    let pairs = vec![
        (1_000_000, 2_000_000),
        (2_000_000, 3_000_000),
        (3_000_000, 1_000_000), // 3-cycle on scattered indices
        (1_000_000, 999_999),   // tree off the cycle
    ];
    run_through(pairs.clone(), new_spc);
    run_through(pairs, sequence_parallel_copies_legacy);
}
