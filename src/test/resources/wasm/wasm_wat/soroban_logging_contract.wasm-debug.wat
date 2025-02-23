(module $soroban_logging_contract.wasm
  (type $t0 (func (param i64) (result i64)))
  (type $t1 (func))
  (func $hello (type $t0) (param $p0 i64) (result i64)
    (local $l1 i32)
    block  ;; label = @1
      local.get $p0
      i32.wrap_i64
      i32.const 255
      i32.and
      local.tee $l1
      i32.const 14
      i32.eq
      br_if 0 (;@1;)
      local.get $l1
      i32.const 74
      i32.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    i64.const 2)
  (func $_ (type $t1))
  (memory $memory 16)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048576))
  (global $__heap_base i32 (i32.const 1048576))
  (export "memory" (memory $memory))
  (export "hello" (func $hello))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base)))
