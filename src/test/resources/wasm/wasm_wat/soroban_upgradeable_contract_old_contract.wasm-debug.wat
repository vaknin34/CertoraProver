(module $soroban_upgradeable_contract_old_contract.wasm
  (type $t0 (func (param i64 i64) (result i64)))
  (type $t1 (func (param i64 i64 i64) (result i64)))
  (type $t2 (func (param i64) (result i64)))
  (type $t3 (func (result i64)))
  (type $t4 (func (param i64) (result i32)))
  (type $t5 (func))
  (import "b" "j" (func $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h1da291d5f4d7d7a0E (type $t0)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h344d68baa0c9d7adE (type $t0)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h55a909d202cb8f43E (type $t1)))
  (import "b" "8" (func $_ZN17soroban_env_guest5guest3buf9bytes_len17hd1d239505ec385e2E (type $t2)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17haab02dae0322886eE (type $t0)))
  (import "a" "0" (func $_ZN17soroban_env_guest5guest7address12require_auth17h6a937218b13952c5E (type $t2)))
  (import "l" "6" (func $_ZN17soroban_env_guest5guest6ledger28update_current_contract_wasm17hcbb148bb17f4ff5fE (type $t2)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17h6533e7e112d73571E (type $t0)))
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17habd63b8447a89eb0E (type $t3) (result i64)
    (local $l0 i32) (local $l1 i64) (local $l2 i32) (local $l3 i32) (local $l4 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    i64.const 0
    local.set $l1
    i32.const -5
    local.set $l2
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l2
            i32.eqz
            br_if 1 (;@3;)
            i32.const 1
            local.set $l3
            block  ;; label = @5
              local.get $l2
              i32.const 1048581
              i32.add
              i32.load8_u
              local.tee $l4
              i32.const 95
              i32.eq
              br_if 0 (;@5;)
              block  ;; label = @6
                local.get $l4
                i32.const -48
                i32.add
                i32.const 255
                i32.and
                i32.const 10
                i32.lt_u
                br_if 0 (;@6;)
                block  ;; label = @7
                  local.get $l4
                  i32.const -65
                  i32.add
                  i32.const 255
                  i32.and
                  i32.const 26
                  i32.lt_u
                  br_if 0 (;@7;)
                  local.get $l4
                  i32.const -97
                  i32.add
                  i32.const 255
                  i32.and
                  i32.const 25
                  i32.gt_u
                  br_if 5 (;@2;)
                  local.get $l4
                  i32.const -59
                  i32.add
                  local.set $l3
                  br 2 (;@5;)
                end
                local.get $l4
                i32.const -53
                i32.add
                local.set $l3
                br 1 (;@5;)
              end
              local.get $l4
              i32.const -46
              i32.add
              local.set $l3
            end
            local.get $l1
            i64.const 6
            i64.shl
            local.get $l3
            i64.extend_i32_u
            i64.const 255
            i64.and
            i64.or
            local.set $l1
            local.get $l2
            i32.const 1
            i32.add
            local.set $l2
            br 0 (;@4;)
          end
        end
        local.get $l1
        i64.const 8
        i64.shl
        i64.const 14
        i64.or
        local.set $l1
        br 1 (;@1;)
      end
      i32.const 1048576
      i64.extend_i32_u
      i64.const 32
      i64.shl
      i64.const 4
      i64.or
      i64.const 21474836484
      call $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h1da291d5f4d7d7a0E
      local.set $l1
    end
    local.get $l0
    local.get $l1
    i64.store offset=8
    local.get $l0
    i32.const 8
    i32.add
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.const 4294967300
    call $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h344d68baa0c9d7adE
    local.set $l1
    local.get $l0
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l1)
  (func $init (type $t2) (param $p0 i64) (result i64)
    (local $l1 i64)
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 77
      i64.ne
      br_if 0 (;@1;)
      i64.const 4294967299
      local.set $l1
      block  ;; label = @2
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17habd63b8447a89eb0E
        call $_ZN11soroban_sdk7storage7Storage12has_internal17h1e4729bef5b3e990E
        br_if 0 (;@2;)
        i64.const 2
        local.set $l1
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17habd63b8447a89eb0E
        local.get $p0
        i64.const 2
        call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h55a909d202cb8f43E
        drop
      end
      local.get $l1
      return
    end
    unreachable
    unreachable)
  (func $_ZN11soroban_sdk7storage7Storage12has_internal17h1e4729bef5b3e990E (type $t4) (param $p0 i64) (result i32)
    local.get $p0
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17h6533e7e112d73571E
    i64.const 1
    i64.eq)
  (func $version (type $t3) (result i64)
    i64.const 4294967300)
  (func $upgrade (type $t2) (param $p0 i64) (result i64)
    (local $l1 i64)
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p0
          i64.const 255
          i64.and
          i64.const 72
          i64.ne
          br_if 0 (;@3;)
          local.get $p0
          call $_ZN17soroban_env_guest5guest3buf9bytes_len17hd1d239505ec385e2E
          i64.const -4294967296
          i64.and
          i64.const 137438953472
          i64.ne
          br_if 0 (;@3;)
          call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17habd63b8447a89eb0E
          local.tee $l1
          call $_ZN11soroban_sdk7storage7Storage12has_internal17h1e4729bef5b3e990E
          i32.eqz
          br_if 1 (;@2;)
          local.get $l1
          i64.const 2
          call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17haab02dae0322886eE
          local.tee $l1
          i64.const 255
          i64.and
          i64.const 77
          i64.eq
          br_if 2 (;@1;)
        end
        unreachable
        unreachable
      end
      call $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E
      unreachable
    end
    local.get $l1
    call $_ZN17soroban_env_guest5guest7address12require_auth17h6a937218b13952c5E
    drop
    local.get $p0
    call $_ZN17soroban_env_guest5guest6ledger28update_current_contract_wasm17hcbb148bb17f4ff5fE
    drop
    i64.const 2)
  (func $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E (type $t5)
    call $_ZN4core9panicking5panic17hcaca2598a27ec0fcE
    unreachable)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t5)
    unreachable
    unreachable)
  (func $_ZN4core9panicking5panic17hcaca2598a27ec0fcE (type $t5)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ (type $t5))
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048581))
  (global $__heap_base i32 (i32.const 1048592))
  (export "memory" (memory $memory))
  (export "init" (func $init))
  (export "version" (func $version))
  (export "upgrade" (func $upgrade))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (data $.rodata (i32.const 1048576) "Admin"))
