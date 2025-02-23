(module $soroban_auth_contract.wasm
  (type $t0 (func (param i64 i64) (result i64)))
  (type $t1 (func (param i64) (result i64)))
  (type $t2 (func (param i64 i64 i64) (result i64)))
  (type $t3 (func))
  (import "b" "j" (func $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h65f4c5e4b5b0b386E (type $t0)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE (type $t0)))
  (import "a" "0" (func $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE (type $t1)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE (type $t0)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E (type $t0)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E (type $t2)))
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h1bfe01766355cce3E (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i64) (local $l3 i32) (local $l4 i32) (local $l5 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    i64.const 0
    local.set $l2
    i32.const -7
    local.set $l3
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l3
            i32.eqz
            br_if 1 (;@3;)
            i32.const 1
            local.set $l4
            block  ;; label = @5
              local.get $l3
              i32.const 1048583
              i32.add
              i32.load8_u
              local.tee $l5
              i32.const 95
              i32.eq
              br_if 0 (;@5;)
              block  ;; label = @6
                local.get $l5
                i32.const -48
                i32.add
                i32.const 255
                i32.and
                i32.const 10
                i32.lt_u
                br_if 0 (;@6;)
                block  ;; label = @7
                  local.get $l5
                  i32.const -65
                  i32.add
                  i32.const 255
                  i32.and
                  i32.const 26
                  i32.lt_u
                  br_if 0 (;@7;)
                  local.get $l5
                  i32.const -97
                  i32.add
                  i32.const 255
                  i32.and
                  i32.const 25
                  i32.gt_u
                  br_if 5 (;@2;)
                  local.get $l5
                  i32.const -59
                  i32.add
                  local.set $l4
                  br 2 (;@5;)
                end
                local.get $l5
                i32.const -53
                i32.add
                local.set $l4
                br 1 (;@5;)
              end
              local.get $l5
              i32.const -46
              i32.add
              local.set $l4
            end
            local.get $l2
            i64.const 6
            i64.shl
            local.get $l4
            i64.extend_i32_u
            i64.const 255
            i64.and
            i64.or
            local.set $l2
            local.get $l3
            i32.const 1
            i32.add
            local.set $l3
            br 0 (;@4;)
          end
        end
        local.get $l2
        i64.const 8
        i64.shl
        i64.const 14
        i64.or
        local.set $l2
        br 1 (;@1;)
      end
      i32.const 1048576
      i64.extend_i32_u
      i64.const 32
      i64.shl
      i64.const 4
      i64.or
      i64.const 30064771076
      call $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h65f4c5e4b5b0b386E
      local.set $l2
    end
    local.get $l1
    local.get $p0
    i64.store offset=8
    local.get $l1
    local.get $l2
    i64.store
    local.get $l1
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.const 8589934596
    call $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE
    local.set $l2
    local.get $l1
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l2)
  (func $increment (type $t0) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32) (local $l3 i64) (local $l4 i32)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i64.const 255
        i64.and
        i64.const 77
        i64.ne
        br_if 0 (;@2;)
        local.get $p1
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 0 (;@2;)
        local.get $p0
        call $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE
        drop
        i32.const 0
        local.set $l2
        block  ;; label = @3
          local.get $p0
          call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h1bfe01766355cce3E
          local.tee $l3
          i64.const 1
          call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE
          i64.const 1
          i64.ne
          br_if 0 (;@3;)
          local.get $l3
          i64.const 1
          call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E
          local.tee $l3
          i64.const 255
          i64.and
          i64.const 4
          i64.ne
          br_if 1 (;@2;)
          local.get $l3
          i64.const 32
          i64.shr_u
          i32.wrap_i64
          local.set $l2
        end
        local.get $l2
        local.get $p1
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        i32.add
        local.tee $l4
        local.get $l2
        i32.lt_u
        br_if 1 (;@1;)
        local.get $p0
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h1bfe01766355cce3E
        local.get $l4
        i64.extend_i32_u
        i64.const 32
        i64.shl
        i64.const 4
        i64.or
        local.tee $p0
        i64.const 1
        call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E
        drop
        local.get $p0
        return
      end
      unreachable
      unreachable
    end
    call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
    unreachable)
  (func $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E (type $t3)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t3)
    unreachable
    unreachable)
  (func $_ (type $t3))
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048583))
  (global $__heap_base i32 (i32.const 1048592))
  (export "memory" (memory $memory))
  (export "increment" (func $increment))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (data $.rodata (i32.const 1048576) "Counter"))
