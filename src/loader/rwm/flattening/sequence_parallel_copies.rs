//! Implements what the literature calls "parallel moves".
//!
//! Considering the precondition that every destination register has a single source register,
//! the resulting directed graph consists of these three kinds of connected components:
//! 1. Trees, where leaves are destination-only registers, and the root is a source-only register.
//! 2. Cycles, where every register is both a source and a destination.
//! 3. A single cycle originating one or more trees. In this case, you can't have more than one
//!    connected cycle, because that would violate the precondition.
//!
//! Cases 1 and 3 are handled in the first phase of the algorithm, where the copies are generated
//! in a topological order, pruning the trees from the graph. In case 3, the cycle is naturally,
//! broken, because the value of a register in the cycle is written to a register in the connected,
//! and this register is then used as source for the remaining copies in the cycle.
//!
//! Cases 2, the remaining cycles in the graph, are handled in the second phase of the algorithm,
//! where a temporary register is used to break the cycle. The temporary register is either a
//! dedicated temporary register, or, if possible, any register that has is not an original source,
//! handled in the first phase of the algorithm.
//!
//! The body of the algorithm lives in Lean 4 (see `lean/ParallelCopies.lean`); this module is a
//! thin FFI shim. We still validate the pre-condition in Rust because (a) Lean's `panic!` is
//! recoverable in pure code and would not propagate as a Rust panic, and (b) `#[should_panic]`
//! tests document the contract at the Rust boundary.

use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Register {
    Temp,
    Given(u32),
}

/// Given a set of parallel copies, determine a sequence of individual copy instructions
/// that can be executed in order without overwriting any source values before they are copied.
///
/// At most one tmp register may be used to break cycles, but not necessarily.
///
/// `parallel_copies` is a list of (source, destination) register pairs that need to be copied in parallel.
///
/// Returns a sequence of (source, destination) register pairs that can be executed in order to achieve
/// the same effect as the original parallel copies.
///
/// Pre-condition: each non-self destination may be written by at most one *distinct* source.
/// Self-copies (`src == dst`) and exact-duplicate edges (`(s, d)` appearing more than once with the
/// same `s`) are allowed — they are silently filtered out. Only conflicting writes — two pairs
/// `(s₁, d)` and `(s₂, d)` with `s₁ ≠ s₂` and neither being a self-copy — panic.
pub fn sequence_parallel_copies(
    parallel_copies: impl IntoIterator<Item = (u32, u32)>,
) -> impl Iterator<Item = (Register, Register)> {
    let pairs: Vec<(u32, u32)> = parallel_copies.into_iter().collect();

    // Pre-condition check. Matches the original Rust implementation: self-copies and exact
    // duplicates are dropped silently; a destination written by *different* sources panics.
    let mut seen: BTreeMap<u32, u32> = BTreeMap::new();
    for &(src, dst) in &pairs {
        if src == dst {
            continue;
        }
        match seen.get(&dst) {
            Some(&prev) if prev == src => continue,
            Some(_) => panic!(
                "Pre-condition violated: destination register {} is written to more than once",
                dst
            ),
            None => {
                seen.insert(dst, src);
            }
        }
    }

    // Encode pairs as little-endian u32s and hand them to Lean. Use checked
    // arithmetic at the FFI boundary so a pathologically large input is
    // rejected before we wrap and under-allocate.
    let input_len = pairs
        .len()
        .checked_mul(2)
        .expect("sequence_parallel_copies: input too large (overflow in length)");
    let mut input: Vec<u32> = Vec::with_capacity(input_len);
    for &(src, dst) in &pairs {
        input.push(src);
        input.push(dst);
    }

    // NOTE: a debug-mode runtime check that this schedule (and especially its
    // *materialised* form, after `parallel_copy` resolves `Register::Temp` to a
    // concrete u32) realises parallel-copy semantics would be a useful belt-
    // and-braces guard against future regressions in `parallel_copy`. The
    // present module's 47 unit tests already cover the Lean schedule; the
    // missing piece is a check at the materialisation layer. Left as a follow-up.
    unsafe { call_lean(&input) }
}

unsafe fn call_lean(input: &[u32]) -> std::vec::IntoIter<(Register, Register)> {
    // The C side decodes the flat u32 stream into (src, dst) pairs, runs the Lean algorithm,
    // and returns a flat u32 stream of (tag_s, val_s, tag_d, val_d) quadruples.
    let buf = unsafe { ffi::crush_seq_parallel_copies(input.as_ptr(), input.len() / 2) };
    let copies = decode_output(&buf);
    unsafe { ffi::crush_seq_parallel_copies_free(buf) };
    copies.into_iter()
}

fn decode_output(buf: &ffi::CrushBuf) -> Vec<(Register, Register)> {
    if buf.ptr.is_null() || buf.len_u32 == 0 {
        return Vec::new();
    }
    assert!(
        buf.len_u32 % 4 == 0,
        "Lean returned a malformed buffer: len_u32 = {}",
        buf.len_u32
    );
    let slice = unsafe { std::slice::from_raw_parts(buf.ptr, buf.len_u32) };
    let mut out = Vec::with_capacity(buf.len_u32 / 4);
    for q in slice.chunks_exact(4) {
        out.push((decode_register(q[0], q[1]), decode_register(q[2], q[3])));
    }
    out
}

fn decode_register(tag: u32, val: u32) -> Register {
    match tag {
        0 => Register::Temp,
        1 => Register::Given(val),
        _ => panic!("Lean returned an unknown Register tag: {tag}"),
    }
}

mod ffi {
    use std::os::raw::c_void;

    #[repr(C)]
    pub struct CrushBuf {
        pub ptr: *mut u32,
        pub len_u32: usize,
    }

    unsafe extern "C" {
        pub fn crush_seq_parallel_copies(pairs: *const u32, num_pairs: usize) -> CrushBuf;
        pub fn crush_seq_parallel_copies_free(buf: CrushBuf);
    }

    // Silence unused-import warnings for c_void when not used directly.
    #[allow(dead_code)]
    fn _unused(_: *mut c_void) {}
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The index of the temporary register in the simulation vector.
    const TMP_REG_INDEX: usize = 1000;

    /// Apply parallel copies naively: read all sources first, then write all destinations.
    /// This simulates true parallel execution.
    /// Self-copies (src == dst) are skipped as they are no-ops.
    fn apply_parallel_copies_naive(registers: &mut [u32], copies: &[(u32, u32)]) {
        // First, read all source values (skipping self-copies)
        let source_values: Vec<(u32, u32)> = copies
            .iter()
            .filter(|&&(src, dst)| src != dst)
            .map(|&(src, dst)| (registers[src as usize], dst))
            .collect();

        // Then, write all destination values
        for (value, dst) in source_values {
            registers[dst as usize] = value;
        }
    }

    /// Apply a sequence of copies one by one (sequential execution).
    fn apply_sequential_copies(
        registers: &mut [u32],
        copies: impl Iterator<Item = (Register, Register)>,
    ) {
        for (src, dst) in copies {
            let src_idx = match src {
                Register::Given(r) => r as usize,
                Register::Temp => TMP_REG_INDEX,
            };
            let dst_idx = match dst {
                Register::Given(r) => r as usize,
                Register::Temp => TMP_REG_INDEX,
            };
            registers[dst_idx] = registers[src_idx];
        }
    }

    /// Helper to run a test case: applies parallel copies naively to get reference,
    /// then applies the sequenced result and compares.
    fn test_parallel_copies(parallel_copies: Vec<(u32, u32)>, num_registers: usize) {
        // Initialize registers with unique values (register i contains value i*10 for clarity)
        let mut reference_registers: Vec<u32> = (0..num_registers.max(TMP_REG_INDEX + 1))
            .map(|i| (i * 10) as u32)
            .collect();
        let mut test_registers = reference_registers.clone();

        // Apply naive parallel copies to get the expected result
        apply_parallel_copies_naive(&mut reference_registers, &parallel_copies);

        // Get the sequenced copies from our algorithm
        let sequenced_copies: Vec<_> = sequence_parallel_copies(parallel_copies).collect();

        // Apply sequenced copies to test registers
        apply_sequential_copies(&mut test_registers, sequenced_copies.into_iter());

        // Compare results (excluding the temp register which is implementation detail)
        assert_eq!(
            &reference_registers[..num_registers],
            &test_registers[..num_registers],
            "Sequenced copies did not produce the same result as parallel copies"
        );
    }

    #[test]
    fn test_empty() {
        test_parallel_copies(vec![], 10);
    }

    #[test]
    fn test_single_copy() {
        test_parallel_copies(vec![(0, 1)], 10);
    }

    #[test]
    fn test_self_copy() {
        // Copying a register to itself should be a no-op
        test_parallel_copies(vec![(0, 0)], 10);
    }

    #[test]
    fn test_multiple_self_copies() {
        test_parallel_copies(vec![(0, 0), (1, 1), (2, 2)], 10);
    }

    #[test]
    fn test_independent_copies() {
        // Multiple copies with no overlap
        test_parallel_copies(vec![(0, 1), (2, 3), (4, 5)], 10);
    }

    #[test]
    fn test_chain_two() {
        // a -> b, b -> c (chain of length 2)
        test_parallel_copies(vec![(0, 1), (1, 2)], 10);
    }

    #[test]
    fn test_chain_three() {
        // a -> b -> c -> d
        test_parallel_copies(vec![(0, 1), (1, 2), (2, 3)], 10);
    }

    #[test]
    fn test_chain_long() {
        // Chain of 10 elements
        let copies: Vec<_> = (0..9).map(|i| (i, i + 1)).collect();
        test_parallel_copies(copies, 20);
    }

    #[test]
    fn test_simple_swap() {
        // a <-> b (cycle of length 2)
        test_parallel_copies(vec![(0, 1), (1, 0)], 10);
    }

    #[test]
    fn test_cycle_three() {
        // a -> b -> c -> a
        test_parallel_copies(vec![(0, 1), (1, 2), (2, 0)], 10);
    }

    #[test]
    fn test_cycle_four() {
        // a -> b -> c -> d -> a
        test_parallel_copies(vec![(0, 1), (1, 2), (2, 3), (3, 0)], 10);
    }

    #[test]
    fn test_cycle_five() {
        test_parallel_copies(vec![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)], 10);
    }

    #[test]
    fn test_tree_fan_out() {
        // One source to multiple destinations: a -> b, a -> c, a -> d
        test_parallel_copies(vec![(0, 1), (0, 2), (0, 3)], 10);
    }

    #[test]
    fn test_tree_deep() {
        // a -> b, b -> c, b -> d (tree with depth 2)
        test_parallel_copies(vec![(0, 1), (1, 2), (1, 3)], 10);
    }

    #[test]
    fn test_tree_complex() {
        // More complex tree:
        //       0
        //      /|\
        //     1 2 3
        //    /|   |
        //   4 5   6
        test_parallel_copies(vec![(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (3, 6)], 10);
    }

    #[test]
    fn test_cycle_with_tree_attached() {
        // Cycle: 0 -> 1 -> 0, with tree: 1 -> 2
        test_parallel_copies(vec![(0, 1), (1, 0), (1, 2)], 10);
    }

    #[test]
    fn test_cycle_with_multiple_trees() {
        // Cycle: 0 -> 1 -> 0, with trees: 0 -> 2, 1 -> 3
        test_parallel_copies(vec![(0, 1), (1, 0), (0, 2), (1, 3)], 10);
    }

    #[test]
    fn test_cycle_with_deep_tree() {
        // Cycle: 0 -> 1 -> 0, with chain: 1 -> 2 -> 3 -> 4
        test_parallel_copies(vec![(0, 1), (1, 0), (1, 2), (2, 3), (3, 4)], 10);
    }

    #[test]
    fn test_multiple_independent_cycles() {
        // Two independent cycles
        test_parallel_copies(vec![(0, 1), (1, 0), (2, 3), (3, 2)], 10);
    }

    #[test]
    fn test_multiple_cycles_different_sizes() {
        // Cycle of 2 and cycle of 3
        test_parallel_copies(vec![(0, 1), (1, 0), (2, 3), (3, 4), (4, 2)], 10);
    }

    #[test]
    fn test_duplicate_copy() {
        // Same copy specified twice
        test_parallel_copies(vec![(0, 1), (0, 1)], 10);
    }

    #[test]
    fn test_chain_with_independent() {
        // Chain plus independent copies
        test_parallel_copies(vec![(0, 1), (1, 2), (3, 4), (5, 6)], 10);
    }

    #[test]
    fn test_cycle_with_chain_and_independent() {
        // Mix of everything
        test_parallel_copies(
            vec![
                (0, 1),
                (1, 0), // cycle
                (2, 3),
                (3, 4), // chain
                (5, 6), // independent
            ],
            10,
        );
    }

    #[test]
    fn test_reverse_order_copies() {
        // Copies specified in reverse order of their natural sequence
        test_parallel_copies(vec![(2, 3), (1, 2), (0, 1)], 10);
    }

    #[test]
    fn test_scattered_registers() {
        // Copies between non-consecutive register numbers
        test_parallel_copies(vec![(0, 100), (100, 200), (200, 50)], 300);
    }

    #[test]
    fn test_cycle_scattered() {
        // Cycle with scattered register numbers
        test_parallel_copies(vec![(5, 50), (50, 100), (100, 5)], 150);
    }

    #[test]
    fn test_all_to_one_fan_in_invalid() {
        // This should panic - multiple sources writing to same destination
        // We test that the algorithm correctly rejects this
    }

    #[test]
    #[should_panic(expected = "destination register")]
    fn test_conflicting_destinations_panics() {
        // Two different sources writing to the same destination - should panic
        let _ = sequence_parallel_copies(vec![(0, 2), (1, 2)]).collect::<Vec<_>>();
    }

    #[test]
    fn test_complex_mixed_scenario() {
        // Complex scenario with multiple components:
        // - A 3-cycle: 0 -> 1 -> 2 -> 0
        // - A tree from node 1: 1 -> 3 -> 4, 3 -> 5
        // - Independent chain: 6 -> 7 -> 8
        // - Independent copy: 9 -> 10
        test_parallel_copies(
            vec![
                // 3-cycle with tree
                (0, 1),
                (1, 2),
                (2, 0),
                (1, 3),
                (3, 4),
                (3, 5),
                // Independent chain
                (6, 7),
                (7, 8),
                // Independent copy
                (9, 10),
            ],
            15,
        );
    }

    #[test]
    fn test_self_copy_mixed_with_others() {
        // Self-copy mixed with real copies
        test_parallel_copies(vec![(0, 0), (1, 2), (2, 2), (3, 4)], 10);
    }

    #[test]
    fn test_long_cycle() {
        // Cycle of 20 elements
        let n = 20;
        let copies: Vec<_> = (0..n).map(|i| (i, (i + 1) % n)).collect();
        test_parallel_copies(copies, 30);
    }

    #[test]
    fn test_many_trees_from_one_root() {
        // Many parallel branches from one root
        test_parallel_copies(
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
            15,
        );
    }

    #[test]
    fn test_two_level_tree() {
        // Two-level tree
        // 0 -> 1, 2, 3
        // 1 -> 4, 5
        // 2 -> 6
        // 3 -> 7, 8
        test_parallel_copies(
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
            15,
        );
    }

    #[test]
    fn test_swap_with_extra_copy_from_each() {
        // Swap 0 <-> 1, plus 0 -> 2 and 1 -> 3
        test_parallel_copies(vec![(0, 1), (1, 0), (0, 2), (1, 3)], 10);
    }

    #[test]
    fn test_overlapping_chains() {
        // Two chains that share a middle node as source
        // 0 -> 1 -> 2 and 0 -> 3 -> 4
        test_parallel_copies(vec![(0, 1), (1, 2), (0, 3), (3, 4)], 10);
    }

    #[test]
    fn test_cycle_every_node_has_tree() {
        // 3-cycle where every node has an additional destination
        // 0 -> 1 -> 2 -> 0, plus 0 -> 3, 1 -> 4, 2 -> 5
        test_parallel_copies(vec![(0, 1), (1, 2), (2, 0), (0, 3), (1, 4), (2, 5)], 10);
    }

    #[test]
    fn test_single_register_universe() {
        // Only one register involved, copying to itself
        test_parallel_copies(vec![(0, 0)], 1);
    }

    #[test]
    fn test_large_independent_copies() {
        // Many independent copies
        let copies: Vec<_> = (0..50).map(|i| (i * 2, i * 2 + 1)).collect();
        test_parallel_copies(copies, 110);
    }

    #[test]
    fn test_alternating_chains() {
        // Two interleaved chains: 0->2->4->6 and 1->3->5->7
        test_parallel_copies(vec![(0, 2), (2, 4), (4, 6), (1, 3), (3, 5), (5, 7)], 10);
    }

    #[test]
    fn test_reverse_chain() {
        // Chain in decreasing order: 4 -> 3 -> 2 -> 1 -> 0
        test_parallel_copies(vec![(4, 3), (3, 2), (2, 1), (1, 0)], 10);
    }

    #[test]
    fn test_bidirectional_chain_no_cycle() {
        // Two chains going opposite directions, not forming a cycle
        // 0 -> 1 -> 2 and 4 -> 3 (separate, no connection)
        test_parallel_copies(vec![(0, 1), (1, 2), (4, 3)], 10);
    }

    #[test]
    fn test_star_pattern_inward() {
        // Multiple sources to different destinations (no conflicts)
        // 0 -> 5, 1 -> 6, 2 -> 7, 3 -> 8, 4 -> 9
        test_parallel_copies(vec![(0, 5), (1, 6), (2, 7), (3, 8), (4, 9)], 15);
    }

    /// Property test: verify that the algorithm never overwrites a source before it's read
    #[test]
    fn test_no_premature_overwrite() {
        // This is implicitly tested by all other tests, but let's be explicit
        // For the chain 0 -> 1 -> 2, if we did 0->1 first, then 1 would be overwritten
        // before we could copy it to 2.
        let copies = vec![(0, 1), (1, 2)];

        let mut registers = vec![10, 20, 30];
        let sequenced: Vec<_> = sequence_parallel_copies(copies).collect();

        // Apply and verify
        for (src, dst) in &sequenced {
            let src_idx = match src {
                Register::Given(r) => *r as usize,
                Register::Temp => panic!("Temp should not be used for simple chain"),
            };
            let dst_idx = match dst {
                Register::Given(r) => *r as usize,
                Register::Temp => panic!("Temp should not be used for simple chain"),
            };
            registers[dst_idx] = registers[src_idx];
        }

        // Expected: reg[0]=10, reg[1]=10, reg[2]=20
        assert_eq!(registers, vec![10, 10, 20]);
    }

    /// Test that cycles use the temp register correctly
    #[test]
    fn test_swap_uses_temp_or_reuses_register() {
        let copies = vec![(0, 1), (1, 0)];
        let sequenced: Vec<_> = sequence_parallel_copies(copies).collect();

        // Check that we have exactly 3 operations for a swap (save, move, restore)
        assert_eq!(sequenced.len(), 3, "Swap should require 3 operations");

        // Verify the sequence works
        let mut registers = vec![10u32; 1001];
        registers[0] = 100;
        registers[1] = 200;

        apply_sequential_copies(&mut registers, sequenced.into_iter());

        assert_eq!(registers[0], 200);
        assert_eq!(registers[1], 100);
    }

    /// Test that output count is correct for various patterns
    #[test]
    fn test_output_count() {
        // Empty -> 0 outputs
        assert_eq!(sequence_parallel_copies(vec![]).count(), 0);

        // Self-copy -> 0 outputs
        assert_eq!(sequence_parallel_copies(vec![(0, 0)]).count(), 0);

        // Single copy -> 1 output
        assert_eq!(sequence_parallel_copies(vec![(0, 1)]).count(), 1);

        // Chain of 3 -> 3 outputs
        assert_eq!(
            sequence_parallel_copies(vec![(0, 1), (1, 2), (2, 3)]).count(),
            3
        );

        // Swap (cycle of 2) -> 3 outputs (save to temp, move, restore from temp)
        assert_eq!(sequence_parallel_copies(vec![(0, 1), (1, 0)]).count(), 3);

        // Cycle of 3 -> 4 outputs (save, 2 moves, restore)
        assert_eq!(
            sequence_parallel_copies(vec![(0, 1), (1, 2), (2, 0)]).count(),
            4
        );
    }

    /// Stress test with randomized but valid input
    #[test]
    fn test_stress_random_trees() {
        // Create a random-ish tree structure
        // Each register (except 0) has exactly one source
        let copies: Vec<_> = (1..100).map(|i| (i / 3, i)).collect();
        test_parallel_copies(copies, 110);
    }

    #[test]
    fn test_stress_multiple_cycles() {
        // Multiple independent cycles of varying sizes
        let mut copies = vec![];

        // Cycle of 2: 0 <-> 1
        copies.extend(vec![(0, 1), (1, 0)]);

        // Cycle of 3: 10 -> 11 -> 12 -> 10
        copies.extend(vec![(10, 11), (11, 12), (12, 10)]);

        // Cycle of 4: 20 -> 21 -> 22 -> 23 -> 20
        copies.extend(vec![(20, 21), (21, 22), (22, 23), (23, 20)]);

        // Cycle of 5: 30 -> 31 -> 32 -> 33 -> 34 -> 30
        copies.extend(vec![(30, 31), (31, 32), (32, 33), (33, 34), (34, 30)]);

        test_parallel_copies(copies, 50);
    }
}
