(module
  (func (export "br_table_two_targets") (param i32) (result i32)
    (block (result i32)
      (block (result i32)
        i32.const 42
        local.get 0
        br_table 0 1
        unreachable
      )
      i32.const 8
      i32.add
    )
  )
)
