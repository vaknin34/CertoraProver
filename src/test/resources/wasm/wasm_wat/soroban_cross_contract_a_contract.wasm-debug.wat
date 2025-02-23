(module $soroban_cross_contract_a_contract.wasm
  (type $t0 (func (param i64 i64) (result i64)))
  (type $t1 (func))
  (func $add (type $t0) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 0 (;@2;)
        local.get $p1
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 0 (;@2;)
        local.get $p0
        i64.const 32
        i64.shr_u
        local.tee $p0
        i32.wrap_i64
        local.tee $l2
        local.get $p1
        i64.const 32
        i64.shr_u
        local.tee $p1
        i32.wrap_i64
        i32.add
        local.get $l2
        i32.lt_u
        br_if 1 (;@1;)
        local.get $p1
        local.get $p0
        i64.add
        i64.const 32
        i64.shl
        i64.const 4
        i64.or
        return
      end
      unreachable
      unreachable
    end
    call $_ZN4core6option13expect_failed17hacfbd4e0f8d6ca3bE
    unreachable)
  (func $_ZN4core6option13expect_failed17hacfbd4e0f8d6ca3bE (type $t1)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t1)
    unreachable
    unreachable)
  (func $_ (type $t1))
  (memory $memory 16)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048576))
  (global $__heap_base i32 (i32.const 1048576))
  (export "memory" (memory $memory))
  (export "add" (func $add))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base)))
