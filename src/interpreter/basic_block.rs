use std::cell::RefCell;
use std::collections::{BTreeMap, btree_map::Entry};
use std::rc::Rc;

use bitflags::bitflags;

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
    struct AccessFlags: u8 {
        const READ = 1 << 0;
        const WRITTEN_EVER = 1 << 1;
        const WRITTEN_LIVE = 1 << 2;
    }
}

/// Assuming each register only need to be read at most once inside a basic block,
/// and written at most once, this struct tracks what registers were accessed in
/// each case. It also tracks whether there are any saves in number of writes,
/// in case the register was written and then dropped before the end of the block.
#[derive(Debug, Default)]
pub struct BasicBlockTracker {
    regs: BTreeMap<u32, AccessFlags>,
    current_block_start: u32,
    per_block_stats: BTreeMap<(u32, u32), BasicBlockExecStats>,
}
impl BasicBlockTracker {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn notify_read(&mut self, reg: u32) {
        match self.regs.entry(reg) {
            Entry::Vacant(entry) => {
                entry.insert(AccessFlags::READ);
            }
            Entry::Occupied(mut entry) => {
                let flags = entry.get_mut();

                // if there is a live write, this read is internal
                // to the block and should not be counted
                if !flags.contains(AccessFlags::WRITTEN_LIVE) {
                    // the only way for we to have !WRITTEN_LIVE && WRITTEN_EVER is for
                    // the register to have been written and then dropped, but in that case
                    // there should not be any reads in a well formed program
                    assert!(!flags.contains(AccessFlags::WRITTEN_EVER));

                    // was never written, so this is an external read, which we do want to track
                    flags.insert(AccessFlags::READ);
                }
            }
        }
    }

    pub fn notify_write(&mut self, reg: u32) {
        let flags = self.regs.entry(reg).or_default();
        flags.insert(AccessFlags::WRITTEN_EVER | AccessFlags::WRITTEN_LIVE);
    }

    pub fn notify_drop(&mut self, reg: u32) {
        if let Some(flags) = self.regs.get_mut(&reg) {
            flags.remove(AccessFlags::WRITTEN_LIVE);
        }
    }

    pub fn notify_drop_from(&mut self, reg: u32) {
        for (_, flags) in self.regs.range_mut(reg..) {
            flags.remove(AccessFlags::WRITTEN_LIVE);
        }
    }

    pub fn reset(&mut self, prev_block_end_pc: u32, next_block_start_pc: u32) {
        // stat block for the just executed block
        let key = (self.current_block_start, prev_block_end_pc);
        let stats = self.per_block_stats.entry(key).or_default();
        stats.times_executed += 1;

        for flags in self.regs.values() {
            let was_read = flags.contains(AccessFlags::READ);
            let was_written_ever = flags.contains(AccessFlags::WRITTEN_EVER);
            let is_written_live = flags.contains(AccessFlags::WRITTEN_LIVE);

            if was_read {
                stats.reads += 1;
            }
            if was_written_ever {
                stats.written_ever += 1;
            }
            if is_written_live {
                stats.written_live += 1;
            }
            if was_read || was_written_ever {
                stats.accesses += 1;
            }
            // A "temporary" access: first touch is a write (no external read)
            // and the value is dropped before the block ends — the register
            // access can be elided entirely.
            if was_written_ever && !is_written_live && !was_read {
                stats.tmp_accesses += 1;
            }
        }

        self.current_block_start = next_block_start_pc;

        // reset for the next block
        self.regs.clear();
    }
}

impl super::BlockBoundaryTracker for Rc<RefCell<BasicBlockTracker>> {
    fn reset(&mut self, prev_block_end_pc: u32, next_block_start_pc: u32) {
        self.borrow_mut()
            .reset(prev_block_end_pc, next_block_start_pc);
    }

    fn print_stats(&self, w: &mut dyn std::io::Write) -> std::io::Result<()> {
        self.borrow().print_stats(w)
    }
}

#[derive(Debug, Default)]
pub struct BasicBlockExecStats {
    pub times_executed: usize,
    pub reads: usize,
    pub written_ever: usize,
    pub written_live: usize,
    pub accesses: usize,
    pub tmp_accesses: usize,
}

impl BasicBlockTracker {
    pub fn print_stats<W: std::io::Write + ?Sized>(&self, w: &mut W) -> std::io::Result<()> {
        // Sort blocks by descending total write cost.
        let mut blocks: Vec<(&(u32, u32), &BasicBlockExecStats)> =
            self.per_block_stats.iter().collect();
        blocks.sort_by_key(|(_, s)| std::cmp::Reverse(s.written_ever));

        writeln!(
            w,
            "{:<20}  {:>10}  {:>10}  {:>12}  {:>12}  {:>10}  {:>12}  {:>8}",
            "block (start..=end)",
            "execs",
            "reads",
            "writes_live",
            "writes_ever",
            "accesses",
            "tmp_accesses",
            "saved%",
        )?;
        writeln!(w, "{}", "-".repeat(103))?;

        let mut total_execs = 0usize;
        let mut total_reads = 0usize;
        let mut total_written_live = 0usize;
        let mut total_written_ever = 0usize;
        let mut total_accesses = 0usize;
        let mut total_tmp_accesses = 0usize;

        for ((start, end), s) in &blocks {
            let saved_pct = if s.accesses == 0 {
                f64::NAN
            } else {
                s.tmp_accesses as f64 / s.accesses as f64 * 100.0
            };

            writeln!(
                w,
                "{:<20}  {:>10}  {:>10}  {:>12}  {:>12}  {:>10}  {:>12}  {:>7.1}%",
                format!("{}..={}", start, end),
                s.times_executed,
                s.reads,
                s.written_live,
                s.written_ever,
                s.accesses,
                s.tmp_accesses,
                saved_pct,
            )?;

            total_execs += s.times_executed;
            total_reads += s.reads;
            total_written_live += s.written_live;
            total_written_ever += s.written_ever;
            total_accesses += s.accesses;
            total_tmp_accesses += s.tmp_accesses;
        }

        let total_saved_pct = if total_accesses == 0 {
            f64::NAN
        } else {
            total_tmp_accesses as f64 / total_accesses as f64 * 100.0
        };

        writeln!(w, "{}", "-".repeat(103))?;
        writeln!(
            w,
            "{:<20}  {:>10}  {:>10}  {:>12}  {:>12}  {:>10}  {:>12}  {:>7.1}%",
            "TOTAL",
            total_execs,
            total_reads,
            total_written_live,
            total_written_ever,
            total_accesses,
            total_tmp_accesses,
            total_saved_pct,
        )?;

        Ok(())
    }
}
