use std::collections::{BTreeMap, HashMap, hash_map::Entry};

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
    regs: HashMap<u32, AccessFlags>,
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
                if flags.contains(AccessFlags::WRITTEN_LIVE) {
                    // there is a live write, so this read is internal
                    // to the block and should not be counted
                    return;
                }
                if flags.contains(AccessFlags::WRITTEN_EVER) {
                    // was once written, but is no longer live (i.e. has been dropped),
                    // now the program is trying to read it.
                    // should not be possible in a well formed program
                    panic!();
                }
                // was never written, so this is an external read, which we do want to track
                flags.insert(AccessFlags::READ);
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

    pub fn reset(&mut self, prev_block_end_pc: u32, next_block_start_pc: u32) {
        // stat block for the just executed block
        let key = (self.current_block_start, prev_block_end_pc);
        let stats = self.per_block_stats.entry(key).or_default();
        stats.times_executed += 1;

        for flags in self.regs.values() {
            if flags.contains(AccessFlags::READ) {
                stats.reads += 1;
            }
            if flags.contains(AccessFlags::WRITTEN_EVER) {
                stats.written_ever += 1;
            }
            if flags.contains(AccessFlags::WRITTEN_LIVE) {
                stats.written_live += 1;
            }
        }

        self.current_block_start = next_block_start_pc;

        // reset for the next block
        self.regs.clear();
    }
}

#[derive(Debug, Default)]
pub struct BasicBlockExecStats {
    pub times_executed: usize,
    pub reads: usize,
    pub written_ever: usize,
    pub written_live: usize,
}

impl BasicBlockTracker {
    pub fn print_stats(&self, w: &mut impl std::io::Write) -> std::io::Result<()> {
        // Sort blocks by descending total write cost.
        let mut blocks: Vec<(&(u32, u32), &BasicBlockExecStats)> =
            self.per_block_stats.iter().collect();
        blocks.sort_by_key(|(_, s)| std::cmp::Reverse(s.written_ever));

        writeln!(
            w,
            "{:<20}  {:>6}  {:>6}  {:>12}  {:>12}  {:>10}  {:>8}",
            "block (start..end)", "execs", "reads", "writes_live", "writes_ever", "saved", "saved%"
        )?;
        writeln!(w, "{}", "-".repeat(83))?;

        let mut total_reads = 0usize;
        let mut total_written_live = 0usize;
        let mut total_written_ever = 0usize;

        for ((start, end), s) in &blocks {
            let saved_pct = if s.written_ever == 0 {
                100.0f64
            } else {
                (1.0 - s.written_live as f64 / s.written_ever as f64) * 100.0
            };

            let saved = s.written_ever - s.written_live;
            writeln!(
                w,
                "{:<20}  {:>6}  {:>6}  {:>12}  {:>12}  {:>10}  {:>7.1}%",
                format!("{}..{}", start, end),
                s.times_executed,
                s.reads,
                s.written_live,
                s.written_ever,
                saved,
                saved_pct,
            )?;

            total_reads += s.reads;
            total_written_live += s.written_live;
            total_written_ever += s.written_ever;
        }

        let total_saved_pct = if total_written_ever == 0 {
            100.0f64
        } else {
            (1.0 - total_written_live as f64 / total_written_ever as f64) * 100.0
        };

        let total_saved = total_written_ever - total_written_live;
        writeln!(w, "{}", "-".repeat(83))?;
        writeln!(
            w,
            "{:<20}  {:>6}  {:>6}  {:>12}  {:>12}  {:>10}  {:>7.1}%",
            "TOTAL",
            "-",
            total_reads,
            total_written_live,
            total_written_ever,
            total_saved,
            total_saved_pct,
        )?;

        Ok(())
    }
}
