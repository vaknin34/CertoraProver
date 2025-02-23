(module $soroban_cross_contract_b_contract.wasm
  (type $t0 (func (param i64 i64) (result i64)))
  (type $t1 (func (param i64 i64 i64) (result i64)))
  (type $t2 (func (param i32)))
  (type $t3 (func))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE (type $t0)))
  (import "d" "_" (func $_ZN17soroban_env_guest5guest4call4call17he38ff75d18335ef7E (type $t1)))
  (func $add_with (type $t1) (param $p0 i64) (param $p1 i64) (param $p2 i64) (result i64)
    (local $l3 i32) (local $l4 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 77
      i64.ne
      br_if 0 (;@1;)
      local.get $p1
      i64.const 255
      i64.and
      i64.const 4
      i64.ne
      br_if 0 (;@1;)
      local.get $p2
      i64.const 255
      i64.and
      i64.const 4
      i64.ne
      br_if 0 (;@1;)
      local.get $l3
      local.get $p2
      i64.const -4294967292
      i64.and
      i64.store offset=8
      local.get $l3
      local.get $p1
      i64.const -4294967292
      i64.and
      i64.store
      i32.const 0
      local.set $l4
      block  ;; label = @2
        loop  ;; label = @3
          block  ;; label = @4
            local.get $l4
            i32.const 16
            i32.ne
            br_if 0 (;@4;)
            i32.const 0
            local.set $l4
            block  ;; label = @5
              loop  ;; label = @6
                local.get $l4
                i32.const 16
                i32.eq
                br_if 1 (;@5;)
                local.get $l3
                i32.const 16
                i32.add
                local.get $l4
                i32.add
                local.get $l3
                local.get $l4
                i32.add
                i64.load
                i64.store
                local.get $l4
                i32.const 8
                i32.add
                local.set $l4
                br 0 (;@6;)
              end
            end
            local.get $p0
            i64.const 40528142
            local.get $l3
            i32.const 16
            i32.add
            i64.extend_i32_u
            i64.const 32
            i64.shl
            i64.const 4
            i64.or
            i64.const 8589934596
            call $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE
            call $_ZN17soroban_env_guest5guest4call4call17he38ff75d18335ef7E
            local.tee $p0
            i64.const 255
            i64.and
            i64.const 4
            i64.ne
            br_if 2 (;@2;)
            local.get $l3
            i32.const 32
            i32.add
            global.set $__stack_pointer
            local.get $p0
            i64.const -4294967292
            i64.and
            return
          end
          local.get $l3
          i32.const 16
          i32.add
          local.get $l4
          i32.add
          i64.const 2
          i64.store
          local.get $l4
          i32.const 8
          i32.add
          local.set $l4
          br 0 (;@3;)
        end
      end
      local.get $l3
      i32.const 16
      i32.add
      call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
      unreachable
    end
    unreachable
    unreachable)
  (func $_ZN4core6result13unwrap_failed17h472431483d5eea7fE (type $t2) (param $p0 i32)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t3)
    unreachable
    unreachable)
  (func $_ (type $t3))
  (memory $memory 16)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048576))
  (global $__heap_base i32 (i32.const 1048576))
  (export "memory" (memory $memory))
  (export "add_with" (func $add_with))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base)))
