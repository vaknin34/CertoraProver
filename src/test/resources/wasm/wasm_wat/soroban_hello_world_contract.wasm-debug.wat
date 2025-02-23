(module $soroban_hello_world_contract.wasm
  (type $t0 (func (param i64 i64) (result i64)))
  (type $t1 (func (param i64) (result i64)))
  (type $t2 (func))
  (import "b" "i" (func $_ZN17soroban_env_guest5guest3buf29string_new_from_linear_memory17h2ece9a81b6f0b712E (type $t0)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE (type $t0)))
  (func $hello (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i64) (local $l3 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 73
      i64.ne
      br_if 0 (;@1;)
      i32.const 1048576
      i64.extend_i32_u
      i64.const 32
      i64.shl
      i64.const 4
      i64.or
      i64.const 21474836484
      call $_ZN17soroban_env_guest5guest3buf29string_new_from_linear_memory17h2ece9a81b6f0b712E
      local.set $l2
      local.get $l1
      local.get $p0
      i64.store offset=8
      local.get $l1
      local.get $l2
      i64.store
      i32.const 0
      local.set $l3
      loop  ;; label = @2
        block  ;; label = @3
          local.get $l3
          i32.const 16
          i32.ne
          br_if 0 (;@3;)
          i32.const 0
          local.set $l3
          block  ;; label = @4
            loop  ;; label = @5
              local.get $l3
              i32.const 16
              i32.eq
              br_if 1 (;@4;)
              local.get $l1
              i32.const 16
              i32.add
              local.get $l3
              i32.add
              local.get $l1
              local.get $l3
              i32.add
              i64.load
              i64.store
              local.get $l3
              i32.const 8
              i32.add
              local.set $l3
              br 0 (;@5;)
            end
          end
          local.get $l1
          i32.const 16
          i32.add
          i64.extend_i32_u
          i64.const 32
          i64.shl
          i64.const 4
          i64.or
          i64.const 8589934596
          call $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE
          local.set $p0
          local.get $l1
          i32.const 32
          i32.add
          global.set $__stack_pointer
          local.get $p0
          return
        end
        local.get $l1
        i32.const 16
        i32.add
        local.get $l3
        i32.add
        i64.const 2
        i64.store
        local.get $l3
        i32.const 8
        i32.add
        local.set $l3
        br 0 (;@2;)
      end
    end
    unreachable
    unreachable)
  (func $_ (type $t2))
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048581))
  (global $__heap_base i32 (i32.const 1048592))
  (export "memory" (memory $memory))
  (export "hello" (func $hello))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (data $.rodata (i32.const 1048576) "Hello"))
