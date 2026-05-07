(module
  ;; Test for the drop-hint algorithm: a local is defined before two nested
  ;; blocks. Inside the innermost block, a `br_if` on the function argument
  ;; exits to depth 0 (after the inner block) where the local is NOT used.
  ;; If the br_if doesn't fire, an unconditional `br 1` exits to depth 1
  ;; (after the outer block) where the local IS used.
  (func $nested_block_drop_hint (param $arg i32) (result i32)
    (local $x i32)

    i32.const 100
    local.set $x

    block       ;; outer block (br target at depth 1 from inside inner)
      block    ;; inner block (br target at depth 0 from inside)
        local.get $arg
        br_if 0    ;; if $arg != 0, exit the inner block
        br 1       ;; otherwise, exit the outer block
      end
      ;; after inner block: does NOT use $x
      i32.const 7
      return
    end
    ;; after outer block: DOES use $x
    local.get $x
    i32.const 1
    i32.add
  )

  (export "nested_block_drop_hint" (func $nested_block_drop_hint))
)
