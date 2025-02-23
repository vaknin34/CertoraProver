(module $soroban_simple_account_contract.wasm
  (type $t0 (func (param i64 i64) (result i64)))
  (type $t1 (func (param i64 i64 i64) (result i64)))
  (type $t2 (func (param i64) (result i64)))
  (type $t3 (func (result i64)))
  (type $t4 (func (param i32 i64)))
  (type $t5 (func (param i64) (result i32)))
  (type $t6 (func))
  (import "b" "j" (func $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h65f4c5e4b5b0b386E (type $t0)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE (type $t0)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E (type $t1)))
  (import "b" "8" (func $_ZN17soroban_env_guest5guest3buf9bytes_len17h783b00115bb1ca2bE (type $t2)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E (type $t0)))
  (import "c" "0" (func $_ZN17soroban_env_guest5guest6crypto18verify_sig_ed2551917hb3129d31d3626aacE (type $t1)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE (type $t0)))
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h7d6bc9a3a857394dE (type $t3) (result i64)
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
      call $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h65f4c5e4b5b0b386E
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
    call $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE
    local.set $l1
    local.get $l0
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l1)
  (func $init (type $t2) (param $p0 i64) (result i64)
    (local $l1 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    local.get $p0
    call $_ZN155_$LT$soroban_sdk..bytes..BytesN$LT$_$GT$$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h44db584ecfeb8fbeE
    block  ;; label = @1
      block  ;; label = @2
        local.get $l1
        i64.load
        i32.wrap_i64
        br_if 0 (;@2;)
        local.get $l1
        i64.load offset=8
        local.set $p0
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h7d6bc9a3a857394dE
        call $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE
        br_if 1 (;@1;)
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h7d6bc9a3a857394dE
        local.get $p0
        i64.const 2
        call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E
        drop
        local.get $l1
        i32.const 16
        i32.add
        global.set $__stack_pointer
        i64.const 2
        return
      end
      unreachable
      unreachable
    end
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN155_$LT$soroban_sdk..bytes..BytesN$LT$_$GT$$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h44db584ecfeb8fbeE (type $t4) (param $p0 i32) (param $p1 i64)
    (local $l2 i64)
    i64.const 1
    local.set $l2
    block  ;; label = @1
      local.get $p1
      i64.const 255
      i64.and
      i64.const 72
      i64.ne
      br_if 0 (;@1;)
      local.get $p1
      call $_ZN17soroban_env_guest5guest3buf9bytes_len17h783b00115bb1ca2bE
      i64.const -4294967296
      i64.and
      i64.const 137438953472
      i64.ne
      i64.extend_i32_u
      local.set $l2
    end
    local.get $p0
    local.get $p1
    i64.store offset=8
    local.get $p0
    local.get $l2
    i64.store)
  (func $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE (type $t5) (param $p0 i64) (result i32)
    local.get $p0
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE
    i64.const 1
    i64.eq)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t6)
    unreachable
    unreachable)
  (func $__check_auth (type $t1) (param $p0 i64) (param $p1 i64) (param $p2 i64) (result i64)
    (local $l3 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    i32.const 16
    i32.add
    local.get $p0
    call $_ZN155_$LT$soroban_sdk..bytes..BytesN$LT$_$GT$$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h44db584ecfeb8fbeE
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $l3
          i64.load offset=16
          i32.wrap_i64
          br_if 0 (;@3;)
          local.get $p1
          i64.const 255
          i64.and
          i64.const 72
          i64.ne
          br_if 0 (;@3;)
          local.get $l3
          i64.load offset=24
          local.set $p0
          local.get $p1
          call $_ZN17soroban_env_guest5guest3buf9bytes_len17h783b00115bb1ca2bE
          i64.const -4294967296
          i64.and
          i64.const 274877906944
          i64.ne
          br_if 0 (;@3;)
          local.get $p2
          i64.const 255
          i64.and
          i64.const 75
          i64.ne
          br_if 0 (;@3;)
          call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h7d6bc9a3a857394dE
          local.tee $p2
          call $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE
          i32.eqz
          br_if 1 (;@2;)
          local.get $l3
          local.get $p2
          i64.const 2
          call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E
          call $_ZN155_$LT$soroban_sdk..bytes..BytesN$LT$_$GT$$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h44db584ecfeb8fbeE
          local.get $l3
          i64.load
          i32.wrap_i64
          i32.eqz
          br_if 2 (;@1;)
        end
        unreachable
        unreachable
      end
      call $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E
      unreachable
    end
    local.get $l3
    i64.load offset=8
    local.get $p0
    local.get $p1
    call $_ZN17soroban_env_guest5guest6crypto18verify_sig_ed2551917hb3129d31d3626aacE
    drop
    local.get $l3
    i32.const 32
    i32.add
    global.set $__stack_pointer
    i64.const 2)
  (func $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E (type $t6)
    call $_ZN4core9panicking5panic17hcaca2598a27ec0fcE
    unreachable)
  (func $_ZN4core9panicking5panic17hcaca2598a27ec0fcE (type $t6)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ (type $t6))
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048581))
  (global $__heap_base i32 (i32.const 1048592))
  (export "memory" (memory $memory))
  (export "init" (func $init))
  (export "__check_auth" (func $__check_auth))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (data $.rodata (i32.const 1048576) "Owner"))
