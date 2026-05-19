(module
  ;; Tests for selector lifetime around br_table. In the first two functions
  ;; the same SSA value is pushed onto the stack twice (via
  ;; `local.tee $arg / local.get $arg`), so the br_table selector and the
  ;; topmost branch argument share a single register. The functions return
  ;; two i32s so that a non-trivial parallel-copy resolution is required at
  ;; the default branch's exit — without forcing a copy, the bug fixed by
  ;; the recent BrTable changes does not manifest.

  ;; --- Case 1: selector value is consumed by the DEFAULT branch ---
  ;; Non-default targets drop both branch arguments and return constants.
  ;; The default branch passes both branch arguments through as the
  ;; function's two return values.
  (func $sel_used_in_default (param $arg i32) (result i32 i32)
    block (result i32 i32)            ;; default
      block (result i32 i32)          ;; idx 1
        block (result i32 i32)        ;; idx 0
          i32.const 7                 ;; branch arg 0 (a distinct value)
          local.get $arg
          i32.const 10
          i32.add
          local.tee $arg              ;; branch arg 1 = arg + 10
          local.get $arg              ;; selector  = arg + 10 (same SSA)
          br_table 0 1 2
        end
        drop drop
        i32.const 1000
        i32.const 1100
        return
      end
      drop drop
      i32.const 1001
      i32.const 1101
      return
    end
    ;; default lands here with [7, arg+10] on the stack — both returned.
  )
  (export "sel_used_in_default" (func $sel_used_in_default))

  ;; --- Case 2: selector value is consumed by ONE specific non-default branch ---
  ;; The middle target (idx 1) passes both branch arguments through as
  ;; the function's results; the other two targets drop them.
  (func $sel_used_in_specific (param $arg i32) (result i32 i32)
    block (result i32 i32)            ;; default
      block (result i32 i32)          ;; idx 1 — keeps the values
        block (result i32 i32)        ;; idx 0
          i32.const 7
          local.get $arg
          i32.const 10
          i32.add
          local.tee $arg
          local.get $arg
          br_table 0 1 2
        end
        drop drop
        i32.const 2000
        i32.const 2100
        return
      end
      ;; idx 1: stack already has [7, arg+10]; both are the function results.
      return
    end
    drop drop
    i32.const 2002
    i32.const 2102
  )
  (export "sel_used_in_specific" (func $sel_used_in_specific))

  ;; --- Case 3: selector value NOT used after br_table ---
  ;; No branch arguments at all; the selector value must be dropped at the
  ;; br_table itself. Each target produces its own constant.
  (func $sel_unused_after_table (param $arg i32) (result i32)
    block                             ;; default
      block                           ;; idx 1
        block                         ;; idx 0
          local.get $arg
          i32.const 10
          i32.add
          br_table 0 1 2
        end
        i32.const 3000
        return
      end
      i32.const 3001
      return
    end
    i32.const 3002
  )
  (export "sel_unused_after_table" (func $sel_unused_after_table))
)
