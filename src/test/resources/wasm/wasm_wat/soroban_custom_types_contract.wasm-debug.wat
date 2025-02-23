(module $soroban_custom_types_contract.wasm
  (type $t0 (func (param i64 i64 i64) (result i64)))
  (type $t1 (func (param i64 i64) (result i64)))
  (type $t2 (func (param i64 i64 i64 i64) (result i64)))
  (type $t3 (func (param i32 i32) (result i64)))
  (type $t4 (func (param i64) (result i64)))
  (type $t5 (func (param i32)))
  (type $t6 (func))
  (type $t7 (func (result i64)))
  (import "m" "9" (func $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17h999916ef23111b0dE (type $t0)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E (type $t0)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE (type $t1)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E (type $t1)))
  (import "m" "a" (func $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h15a7786289874722E (type $t2)))
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h24fc483822e431a9E (type $t3) (param $p0 i32) (param $p1 i32) (result i64)
    (local $l2 i32) (local $l3 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    local.get $p1
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.store offset=8
    local.get $l2
    local.get $p0
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.store
    i32.const 1048592
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    local.get $l2
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.const 8589934596
    call $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17h999916ef23111b0dE
    local.set $l3
    local.get $l2
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l3)
  (func $increment (type $t4) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i32) (local $l3 i32) (local $l4 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 0 (;@2;)
        local.get $l1
        i32.const 8
        i32.add
        call $_ZN29soroban_custom_types_contract17IncrementContract9get_state17hed41685411b115d2E
        local.get $l1
        i32.load offset=8
        local.tee $l2
        local.get $p0
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        local.tee $l3
        i32.add
        local.tee $l4
        local.get $l2
        i32.lt_u
        br_if 1 (;@1;)
        i64.const 130942488590
        local.get $l4
        local.get $l3
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h24fc483822e431a9E
        i64.const 2
        call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E
        drop
        local.get $l1
        i32.const 16
        i32.add
        global.set $__stack_pointer
        local.get $l4
        i64.extend_i32_u
        i64.const 32
        i64.shl
        i64.const 4
        i64.or
        return
      end
      unreachable
      unreachable
    end
    call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
    unreachable)
  (func $_ZN29soroban_custom_types_contract17IncrementContract9get_state17hed41685411b115d2E (type $t5) (param $p0 i32)
    (local $l1 i32) (local $l2 i32) (local $l3 i32) (local $l4 i64) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    i32.const 0
    local.set $l2
    i32.const 0
    local.set $l3
    block  ;; label = @1
      block  ;; label = @2
        i64.const 130942488590
        i64.const 2
        call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE
        i64.const 1
        i64.ne
        br_if 0 (;@2;)
        i64.const 130942488590
        i64.const 2
        call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E
        local.set $l4
        i32.const 0
        local.set $l2
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l2
            i32.const 16
            i32.eq
            br_if 1 (;@3;)
            local.get $l1
            local.get $l2
            i32.add
            i64.const 2
            i64.store
            local.get $l2
            i32.const 8
            i32.add
            local.set $l2
            br 0 (;@4;)
          end
        end
        local.get $l4
        i64.const 255
        i64.and
        i64.const 76
        i64.ne
        br_if 1 (;@1;)
        local.get $l4
        i32.const 1048592
        i64.extend_i32_u
        i64.const 32
        i64.shl
        i64.const 4
        i64.or
        local.get $l1
        i64.extend_i32_u
        i64.const 32
        i64.shl
        i64.const 4
        i64.or
        i64.const 8589934596
        call $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h15a7786289874722E
        drop
        local.get $l1
        i64.load
        local.tee $l4
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 1 (;@1;)
        local.get $l1
        i64.load offset=8
        local.tee $l5
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 1 (;@1;)
        local.get $l4
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        local.set $l2
        local.get $l5
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        local.set $l3
      end
      local.get $p0
      local.get $l3
      i32.store offset=4
      local.get $p0
      local.get $l2
      i32.store
      local.get $l1
      i32.const 16
      i32.add
      global.set $__stack_pointer
      return
    end
    unreachable
    unreachable)
  (func $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E (type $t6)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $get_state (type $t7) (result i64)
    (local $l0 i32) (local $l1 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    i32.const 8
    i32.add
    call $_ZN29soroban_custom_types_contract17IncrementContract9get_state17hed41685411b115d2E
    local.get $l0
    i32.load offset=8
    local.get $l0
    i32.load offset=12
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h24fc483822e431a9E
    local.set $l1
    local.get $l0
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l1)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t6)
    unreachable
    unreachable)
  (func $_ (type $t6))
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048608))
  (global $__heap_base i32 (i32.const 1048608))
  (export "memory" (memory $memory))
  (export "increment" (func $increment))
  (export "get_state" (func $get_state))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (data $.rodata (i32.const 1048576) "countlast_incr\00\00\00\00\10\00\05\00\00\00\05\00\10\00\09\00\00\00"))
