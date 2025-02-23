(module $soroban_single_offer_contract.wasm
  (type $t0 (func (param i64 i64 i64) (result i64)))
  (type $t1 (func (param i64 i64) (result i64)))
  (type $t2 (func (param i64 i64 i64 i64) (result i64)))
  (type $t3 (func (param i64) (result i64)))
  (type $t4 (func (result i64)))
  (type $t5 (func (param i32) (result i64)))
  (type $t6 (func (param i32 i32) (result i64)))
  (type $t7 (func (param i32)))
  (type $t8 (func (param i64) (result i32)))
  (type $t9 (func))
  (type $t10 (func (param i64 i64 i64 i64 i64) (result i64)))
  (type $t11 (func (param i32 i64)))
  (type $t12 (func (param i64 i64 i64 i64 i64)))
  (type $t13 (func (param i32 i64 i64 i64 i64)))
  (type $t14 (func (param i32 i64 i64 i32)))
  (type $t15 (func (param i32 i64 i64 i64 i64 i32)))
  (import "m" "9" (func $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17h999916ef23111b0dE (type $t0)))
  (import "b" "j" (func $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h65f4c5e4b5b0b386E (type $t1)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E (type $t1)))
  (import "m" "a" (func $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h15a7786289874722E (type $t2)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E (type $t0)))
  (import "a" "0" (func $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE (type $t3)))
  (import "x" "7" (func $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h145672d3b76b8d44E (type $t4)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE (type $t1)))
  (import "i" "8" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_hi6417h96047db195ed49dfE (type $t3)))
  (import "i" "7" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_lo6417hda737eee8cb86207E (type $t3)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE (type $t1)))
  (import "i" "6" (func $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17ha9df624d96cf2a1dE (type $t1)))
  (import "d" "_" (func $_ZN17soroban_env_guest5guest4call4call17he38ff75d18335ef7E (type $t0)))
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h1501b443c8d01348E (type $t5) (param $p0 i32) (result i64)
    (local $l1 i32) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    local.get $p0
    i64.load
    i64.store offset=40
    local.get $l1
    local.get $p0
    i64.load offset=8
    i64.store offset=32
    local.get $l1
    local.get $p0
    i64.load offset=16
    i64.store offset=16
    local.get $l1
    local.get $p0
    i64.load32_u offset=24
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.store offset=24
    local.get $l1
    local.get $p0
    i64.load32_u offset=28
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.store offset=8
    i32.const 1048628
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    local.get $l1
    i32.const 8
    i32.add
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.const 21474836484
    call $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17h999916ef23111b0dE
    local.set $l2
    local.get $l1
    i32.const 48
    i32.add
    global.set $__stack_pointer
    local.get $l2)
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h2f5b3428ee2f44eeE (type $t4) (result i64)
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
    i32.const 1
    call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E
    local.set $l1
    local.get $l0
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l1)
  (func $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E (type $t6) (param $p0 i32) (param $p1 i32) (result i64)
    local.get $p0
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    local.get $p1
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    call $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE)
  (func $_ZN29soroban_single_offer_contract10load_offer17h46a0f38e608b2ddeE (type $t7) (param $p0 i32)
    (local $l1 i32) (local $l2 i64) (local $l3 i32) (local $l4 i64) (local $l5 i64) (local $l6 i64) (local $l7 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h2f5b3428ee2f44eeE
        local.tee $l2
        call $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE
        i32.eqz
        br_if 0 (;@2;)
        local.get $l2
        i64.const 2
        call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E
        local.set $l2
        i32.const 0
        local.set $l3
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l3
            i32.const 40
            i32.eq
            br_if 1 (;@3;)
            local.get $l1
            i32.const 8
            i32.add
            local.get $l3
            i32.add
            i64.const 2
            i64.store
            local.get $l3
            i32.const 8
            i32.add
            local.set $l3
            br 0 (;@4;)
          end
        end
        block  ;; label = @3
          local.get $l2
          i64.const 255
          i64.and
          i64.const 76
          i64.ne
          br_if 0 (;@3;)
          local.get $l2
          i32.const 1048628
          i64.extend_i32_u
          i64.const 32
          i64.shl
          i64.const 4
          i64.or
          local.get $l1
          i32.const 8
          i32.add
          i64.extend_i32_u
          i64.const 32
          i64.shl
          i64.const 4
          i64.or
          i64.const 21474836484
          call $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h15a7786289874722E
          drop
          local.get $l1
          i64.load offset=8
          local.tee $l2
          i64.const 255
          i64.and
          i64.const 4
          i64.ne
          br_if 0 (;@3;)
          local.get $l1
          i64.load offset=16
          local.tee $l4
          i64.const 255
          i64.and
          i64.const 77
          i64.ne
          br_if 0 (;@3;)
          local.get $l1
          i64.load offset=24
          local.tee $l5
          i64.const 255
          i64.and
          i64.const 4
          i64.ne
          br_if 0 (;@3;)
          local.get $l1
          i64.load offset=32
          local.tee $l6
          i64.const 255
          i64.and
          i64.const 77
          i64.ne
          br_if 0 (;@3;)
          local.get $l1
          i64.load offset=40
          local.tee $l7
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
    local.get $p0
    local.get $l4
    i64.store offset=16
    local.get $p0
    local.get $l6
    i64.store offset=8
    local.get $p0
    local.get $l7
    i64.store
    local.get $p0
    local.get $l2
    i64.const 32
    i64.shr_u
    i64.store32 offset=28
    local.get $p0
    local.get $l5
    i64.const 32
    i64.shr_u
    i64.store32 offset=24
    local.get $l1
    i32.const 48
    i32.add
    global.set $__stack_pointer)
  (func $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE (type $t8) (param $p0 i64) (result i32)
    local.get $p0
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE
    i64.const 1
    i64.eq)
  (func $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E (type $t9)
    call $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E
    unreachable)
  (func $_ZN29soroban_single_offer_contract11write_offer17h24c7f583c8bbc3c1E (type $t7) (param $p0 i32)
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h2f5b3428ee2f44eeE
    local.get $p0
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h1501b443c8d01348E
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E
    drop)
  (func $create (type $t10) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64) (result i64)
    (local $l5 i32) (local $l6 i32) (local $l7 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l5
    global.set $__stack_pointer
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
        i64.const 77
        i64.ne
        br_if 0 (;@2;)
        local.get $p2
        i64.const 255
        i64.and
        i64.const 77
        i64.ne
        br_if 0 (;@2;)
        local.get $p3
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 0 (;@2;)
        local.get $p4
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 0 (;@2;)
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h2f5b3428ee2f44eeE
        call $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE
        br_if 1 (;@1;)
        local.get $p3
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        local.tee $l6
        i32.eqz
        br_if 1 (;@1;)
        local.get $p4
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        local.tee $l7
        i32.eqz
        br_if 1 (;@1;)
        local.get $p0
        call $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE
        drop
        local.get $l5
        local.get $l7
        i32.store offset=28
        local.get $l5
        local.get $l6
        i32.store offset=24
        local.get $l5
        local.get $p2
        i64.store offset=16
        local.get $l5
        local.get $p1
        i64.store offset=8
        local.get $l5
        local.get $p0
        i64.store
        local.get $l5
        call $_ZN29soroban_single_offer_contract11write_offer17h24c7f583c8bbc3c1E
        local.get $l5
        i32.const 32
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
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t9)
    unreachable
    unreachable)
  (func $trade (type $t0) (param $p0 i64) (param $p1 i64) (param $p2 i64) (result i64)
    (local $l3 i32) (local $l4 i32) (local $l5 i64) (local $l6 i64) (local $l7 i64) (local $l8 i64) (local $l9 i64)
    global.get $__stack_pointer
    i32.const 80
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p0
          i64.const 255
          i64.and
          i64.const 77
          i64.ne
          br_if 0 (;@3;)
          local.get $l3
          i32.const 48
          i32.add
          local.get $p1
          call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
          local.get $l3
          i64.load offset=48
          i64.eqz
          i32.eqz
          br_if 0 (;@3;)
          local.get $l3
          i32.const 64
          i32.add
          local.tee $l4
          i64.load
          local.set $p1
          local.get $l3
          i64.load offset=56
          local.set $l5
          local.get $l3
          i32.const 48
          i32.add
          local.get $p2
          call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
          local.get $l3
          i64.load offset=48
          i64.eqz
          i32.eqz
          br_if 0 (;@3;)
          local.get $l4
          i64.load
          local.set $p2
          local.get $l3
          i64.load offset=56
          local.set $l6
          local.get $p0
          call $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE
          drop
          local.get $l3
          i32.const 0
          i32.store offset=44
          local.get $l3
          i32.const 48
          i32.add
          call $_ZN29soroban_single_offer_contract10load_offer17h46a0f38e608b2ddeE
          local.get $l3
          i32.const 24
          i32.add
          local.get $l5
          local.get $p1
          local.get $l3
          i64.load32_u offset=72
          i64.const 0
          local.get $l3
          i32.const 44
          i32.add
          call $__muloti4
          local.get $l3
          i32.load offset=44
          br_if 0 (;@3;)
          local.get $l3
          i32.load offset=76
          local.tee $l4
          i32.eqz
          br_if 1 (;@2;)
          local.get $l3
          i64.load offset=64
          local.set $l7
          local.get $l3
          i64.load offset=56
          local.set $l8
          local.get $l3
          i32.const 8
          i32.add
          local.get $l3
          i64.load offset=24
          local.get $l3
          i32.const 32
          i32.add
          i64.load
          local.get $l4
          i64.extend_i32_u
          i64.const 0
          call $__divti3
          local.get $l3
          i64.load offset=8
          local.tee $l9
          local.get $l6
          i64.ge_u
          local.get $l3
          i32.const 16
          i32.add
          i64.load
          local.tee $l6
          local.get $p2
          i64.ge_s
          local.get $l6
          local.get $p2
          i64.eq
          select
          i32.eqz
          br_if 2 (;@1;)
          local.get $l7
          local.get $p0
          call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h145672d3b76b8d44E
          local.tee $p2
          local.get $l5
          local.get $p1
          call $_ZN11soroban_sdk5token11TokenClient8transfer17hcda477fbab82fc4dE
          local.get $l8
          local.get $p2
          local.get $p0
          local.get $l9
          local.get $l6
          call $_ZN11soroban_sdk5token11TokenClient8transfer17hcda477fbab82fc4dE
          local.get $l7
          local.get $p2
          local.get $l3
          i64.load offset=48
          local.get $l5
          local.get $p1
          call $_ZN11soroban_sdk5token11TokenClient8transfer17hcda477fbab82fc4dE
          local.get $l3
          i32.const 80
          i32.add
          global.set $__stack_pointer
          i64.const 2
          return
        end
        unreachable
        unreachable
      end
      call $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E
      unreachable
    end
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE (type $t11) (param $p0 i32) (param $p1 i64)
    (local $l2 i32) (local $l3 i64)
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p1
          i32.wrap_i64
          i32.const 255
          i32.and
          local.tee $l2
          i32.const 69
          i32.eq
          br_if 0 (;@3;)
          local.get $l2
          i32.const 11
          i32.ne
          br_if 1 (;@2;)
          local.get $p0
          i32.const 16
          i32.add
          local.get $p1
          i64.const 63
          i64.shr_s
          i64.store
          local.get $p0
          local.get $p1
          i64.const 8
          i64.shr_s
          i64.store offset=8
          i64.const 0
          local.set $p1
          br 2 (;@1;)
        end
        local.get $p1
        call $_ZN17soroban_env_guest5guest3int16obj_to_i128_hi6417h96047db195ed49dfE
        local.set $l3
        local.get $p1
        call $_ZN17soroban_env_guest5guest3int16obj_to_i128_lo6417hda737eee8cb86207E
        local.set $p1
        local.get $p0
        i32.const 16
        i32.add
        local.get $l3
        i64.store
        local.get $p0
        local.get $p1
        i64.store offset=8
        i64.const 0
        local.set $p1
        br 1 (;@1;)
      end
      local.get $p0
      i64.const 34359740419
      i64.store offset=8
      i64.const 1
      local.set $p1
    end
    local.get $p0
    local.get $p1
    i64.store)
  (func $_ZN11soroban_sdk5token11TokenClient8transfer17hcda477fbab82fc4dE (type $t12) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64)
    (local $l5 i32) (local $l6 i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l5
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        local.get $p3
        i64.const 36028797018963968
        i64.add
        i64.const 72057594037927935
        i64.gt_u
        br_if 0 (;@2;)
        local.get $p3
        local.get $p3
        i64.xor
        local.get $p3
        i64.const 63
        i64.shr_s
        local.get $p4
        i64.xor
        i64.or
        i64.const 0
        i64.ne
        br_if 0 (;@2;)
        local.get $p3
        i64.const 8
        i64.shl
        i64.const 11
        i64.or
        local.set $p3
        br 1 (;@1;)
      end
      local.get $p4
      local.get $p3
      call $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17ha9df624d96cf2a1dE
      local.set $p3
    end
    local.get $l5
    local.get $p3
    i64.store offset=16
    local.get $l5
    local.get $p2
    i64.store offset=8
    local.get $l5
    local.get $p1
    i64.store
    i32.const 0
    local.set $l6
    block  ;; label = @1
      loop  ;; label = @2
        block  ;; label = @3
          local.get $l6
          i32.const 24
          i32.ne
          br_if 0 (;@3;)
          i32.const 0
          local.set $l6
          block  ;; label = @4
            loop  ;; label = @5
              local.get $l6
              i32.const 24
              i32.eq
              br_if 1 (;@4;)
              local.get $l5
              i32.const 24
              i32.add
              local.get $l6
              i32.add
              local.get $l5
              local.get $l6
              i32.add
              i64.load
              i64.store
              local.get $l6
              i32.const 8
              i32.add
              local.set $l6
              br 0 (;@5;)
            end
          end
          local.get $p0
          i64.const 65154533130155790
          local.get $l5
          i32.const 24
          i32.add
          i32.const 3
          call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E
          call $_ZN17soroban_env_guest5guest4call4call17he38ff75d18335ef7E
          i64.const 255
          i64.and
          i64.const 2
          i64.ne
          br_if 2 (;@1;)
          local.get $l5
          i32.const 48
          i32.add
          global.set $__stack_pointer
          return
        end
        local.get $l5
        i32.const 24
        i32.add
        local.get $l6
        i32.add
        i64.const 2
        i64.store
        local.get $l6
        i32.const 8
        i32.add
        local.set $l6
        br 0 (;@2;)
      end
    end
    local.get $l5
    i32.const 24
    i32.add
    call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
    unreachable)
  (func $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E (type $t9)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $withdraw (type $t1) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32) (local $l3 i64) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 77
      i64.ne
      br_if 0 (;@1;)
      local.get $l2
      local.get $p1
      call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
      local.get $l2
      i64.load
      i64.eqz
      i32.eqz
      br_if 0 (;@1;)
      local.get $l2
      i32.const 16
      i32.add
      i64.load
      local.set $p1
      local.get $l2
      i64.load offset=8
      local.set $l3
      local.get $l2
      call $_ZN29soroban_single_offer_contract10load_offer17h46a0f38e608b2ddeE
      local.get $l2
      i64.load
      local.tee $l4
      call $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE
      drop
      local.get $p0
      call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h145672d3b76b8d44E
      local.get $l4
      local.get $l3
      local.get $p1
      call $_ZN11soroban_sdk5token11TokenClient8transfer17hcda477fbab82fc4dE
      local.get $l2
      i32.const 32
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    unreachable
    unreachable)
  (func $updt_price (type $t1) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32) (local $l3 i32) (local $l4 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
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
        i32.wrap_i64
        local.tee $l3
        i32.eqz
        br_if 1 (;@1;)
        local.get $p1
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        local.tee $l4
        i32.eqz
        br_if 1 (;@1;)
        local.get $l2
        call $_ZN29soroban_single_offer_contract10load_offer17h46a0f38e608b2ddeE
        local.get $l2
        i64.load
        call $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE
        drop
        local.get $l2
        local.get $l4
        i32.store offset=28
        local.get $l2
        local.get $l3
        i32.store offset=24
        local.get $l2
        call $_ZN29soroban_single_offer_contract11write_offer17h24c7f583c8bbc3c1E
        local.get $l2
        i32.const 32
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
  (func $get_offer (type $t4) (result i64)
    (local $l0 i32) (local $l1 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    call $_ZN29soroban_single_offer_contract10load_offer17h46a0f38e608b2ddeE
    local.get $l0
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h1501b443c8d01348E
    local.set $l1
    local.get $l0
    i32.const 32
    i32.add
    global.set $__stack_pointer
    local.get $l1)
  (func $_ZN4core6result13unwrap_failed17h472431483d5eea7fE (type $t7) (param $p0 i32)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ (type $t9))
  (func $_ZN17compiler_builtins3int19specialized_div_rem12u128_div_rem17h037f7f51afb6bf78E (type $t13) (param $p0 i32) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64)
    (local $l5 i32) (local $l6 i64) (local $l7 i32) (local $l8 i64) (local $l9 i64) (local $l10 i64) (local $l11 i64) (local $l12 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l5
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              local.get $p3
              i64.eqz
              br_if 0 (;@5;)
              local.get $p4
              i64.eqz
              br_if 1 (;@4;)
            end
            i64.const 0
            local.set $l6
            local.get $p1
            local.get $p3
            i64.lt_u
            local.get $p2
            local.get $p4
            i64.lt_u
            local.get $p2
            local.get $p4
            i64.eq
            select
            br_if 1 (;@3;)
            local.get $p2
            i64.eqz
            br_if 1 (;@3;)
            local.get $l5
            i32.const 16
            i32.add
            local.get $p3
            local.get $p4
            local.get $p4
            i64.clz
            i32.wrap_i64
            local.get $p2
            i64.clz
            i32.wrap_i64
            i32.sub
            local.tee $l7
            i32.const 127
            i32.and
            call $__ashlti3
            i64.const 1
            local.get $l7
            i32.const 63
            i32.and
            i64.extend_i32_u
            i64.shl
            local.set $l8
            local.get $l5
            i32.const 24
            i32.add
            i64.load
            local.set $l9
            local.get $l5
            i64.load offset=16
            local.set $l10
            i64.const 0
            local.set $l6
            loop  ;; label = @5
              block  ;; label = @6
                local.get $p2
                local.get $l9
                i64.sub
                local.get $p1
                local.get $l10
                i64.lt_u
                i64.extend_i32_u
                i64.sub
                local.tee $l11
                i64.const 0
                i64.lt_s
                br_if 0 (;@6;)
                local.get $l8
                local.get $l6
                i64.or
                local.set $l6
                local.get $p1
                local.get $l10
                i64.sub
                local.tee $p1
                local.get $p3
                i64.lt_u
                local.get $l11
                local.get $p4
                i64.lt_u
                local.get $l11
                local.get $p4
                i64.eq
                select
                br_if 4 (;@2;)
                local.get $l11
                local.set $p2
              end
              local.get $l10
              i64.const 1
              i64.shr_u
              local.get $l9
              i64.const 63
              i64.shl
              i64.or
              local.set $l10
              local.get $l8
              i64.const 1
              i64.shr_u
              local.set $l8
              local.get $l9
              i64.const 1
              i64.shr_u
              local.set $l9
              br 0 (;@5;)
            end
          end
          block  ;; label = @4
            block  ;; label = @5
              local.get $p2
              i64.eqz
              br_if 0 (;@5;)
              block  ;; label = @6
                local.get $p2
                local.get $p3
                i64.lt_u
                br_if 0 (;@6;)
                block  ;; label = @7
                  local.get $p2
                  local.get $p3
                  i64.eq
                  br_if 0 (;@7;)
                  local.get $p2
                  local.get $p2
                  local.get $p3
                  i64.div_u
                  local.tee $l12
                  local.get $p3
                  i64.mul
                  i64.sub
                  local.set $l11
                  block  ;; label = @8
                    local.get $p3
                    i64.const 4294967295
                    i64.gt_u
                    br_if 0 (;@8;)
                    local.get $l11
                    i64.const 32
                    i64.shl
                    local.get $p1
                    i64.const 32
                    i64.shr_u
                    i64.or
                    local.tee $l9
                    local.get $l9
                    local.get $p3
                    i64.div_u
                    local.tee $l9
                    local.get $p3
                    i64.mul
                    i64.sub
                    i64.const 32
                    i64.shl
                    local.get $p1
                    i64.const 4294967295
                    i64.and
                    i64.or
                    local.tee $p1
                    local.get $p1
                    local.get $p3
                    i64.div_u
                    local.tee $l10
                    local.get $p3
                    i64.mul
                    i64.sub
                    local.set $p1
                    local.get $l9
                    i64.const 32
                    i64.shl
                    local.get $l10
                    i64.or
                    local.set $l6
                    local.get $l9
                    i64.const 32
                    i64.shr_u
                    local.get $l12
                    i64.or
                    local.set $l12
                    i64.const 0
                    local.set $l11
                    br 7 (;@1;)
                  end
                  local.get $p1
                  local.get $p3
                  i64.lt_u
                  local.get $l11
                  local.get $p4
                  i64.lt_u
                  local.get $l11
                  local.get $p4
                  i64.eq
                  select
                  br_if 3 (;@4;)
                  local.get $p4
                  i64.const 63
                  i64.shl
                  local.get $p3
                  i64.const 1
                  i64.shr_u
                  i64.or
                  local.set $l9
                  local.get $p3
                  i64.const 63
                  i64.shl
                  local.set $l10
                  i64.const -9223372036854775808
                  local.set $p2
                  i64.const 0
                  local.set $p4
                  block  ;; label = @8
                    loop  ;; label = @9
                      block  ;; label = @10
                        local.get $l11
                        local.get $l9
                        i64.sub
                        local.get $p1
                        local.get $l10
                        i64.lt_u
                        i64.extend_i32_u
                        i64.sub
                        local.tee $l8
                        i64.const 0
                        i64.lt_s
                        br_if 0 (;@10;)
                        local.get $p1
                        local.get $l10
                        i64.sub
                        local.set $p1
                        local.get $p2
                        local.get $p4
                        i64.or
                        local.set $p4
                        local.get $l8
                        i64.eqz
                        br_if 2 (;@8;)
                        local.get $l8
                        local.set $l11
                      end
                      local.get $l10
                      i64.const 1
                      i64.shr_u
                      local.get $l9
                      i64.const 63
                      i64.shl
                      i64.or
                      local.set $l10
                      local.get $p2
                      i64.const 1
                      i64.shr_u
                      local.set $p2
                      local.get $l9
                      i64.const 1
                      i64.shr_u
                      local.set $l9
                      br 0 (;@9;)
                    end
                  end
                  local.get $p1
                  local.get $p3
                  i64.div_u
                  local.tee $l9
                  local.get $p4
                  i64.or
                  local.set $l6
                  local.get $p1
                  local.get $l9
                  local.get $p3
                  i64.mul
                  i64.sub
                  local.set $p1
                  i64.const 0
                  local.set $l11
                  br 6 (;@1;)
                end
                local.get $p1
                local.get $p1
                local.get $p2
                i64.div_u
                local.tee $l6
                local.get $p2
                i64.mul
                i64.sub
                local.set $p1
                i64.const 0
                local.set $l11
                i64.const 1
                local.set $l12
                br 5 (;@1;)
              end
              local.get $l5
              local.get $p3
              local.get $p4
              i32.const 63
              local.get $p3
              i64.clz
              local.tee $l9
              i32.wrap_i64
              local.get $p2
              i64.clz
              local.tee $l10
              i32.wrap_i64
              i32.sub
              i32.const 64
              i32.add
              local.get $l10
              local.get $l9
              i64.eq
              select
              local.tee $l7
              call $__ashlti3
              i64.const 1
              local.get $l7
              i32.const 63
              i32.and
              i64.extend_i32_u
              i64.shl
              local.set $l11
              local.get $l5
              i32.const 8
              i32.add
              i64.load
              local.set $l9
              local.get $l5
              i64.load
              local.set $l10
              i64.const 0
              local.set $p4
              block  ;; label = @6
                loop  ;; label = @7
                  block  ;; label = @8
                    local.get $p2
                    local.get $l9
                    i64.sub
                    local.get $p1
                    local.get $l10
                    i64.lt_u
                    i64.extend_i32_u
                    i64.sub
                    local.tee $l8
                    i64.const 0
                    i64.lt_s
                    br_if 0 (;@8;)
                    local.get $p1
                    local.get $l10
                    i64.sub
                    local.set $p1
                    local.get $l11
                    local.get $p4
                    i64.or
                    local.set $p4
                    local.get $l8
                    i64.eqz
                    br_if 2 (;@6;)
                    local.get $l8
                    local.set $p2
                  end
                  local.get $l10
                  i64.const 1
                  i64.shr_u
                  local.get $l9
                  i64.const 63
                  i64.shl
                  i64.or
                  local.set $l10
                  local.get $l11
                  i64.const 1
                  i64.shr_u
                  local.set $l11
                  local.get $l9
                  i64.const 1
                  i64.shr_u
                  local.set $l9
                  br 0 (;@7;)
                end
              end
              local.get $p1
              local.get $p3
              i64.div_u
              local.tee $l9
              local.get $p4
              i64.or
              local.set $l6
              local.get $p1
              local.get $l9
              local.get $p3
              i64.mul
              i64.sub
              local.set $p1
              i64.const 0
              local.set $l11
              br 3 (;@2;)
            end
            local.get $p1
            local.get $p1
            local.get $p3
            i64.div_u
            local.tee $l6
            local.get $p3
            i64.mul
            i64.sub
            local.set $p1
            i64.const 0
            local.set $l11
            br 2 (;@2;)
          end
          i64.const 0
          local.set $l6
          br 2 (;@1;)
        end
        local.get $p2
        local.set $l11
      end
      i64.const 0
      local.set $l12
    end
    local.get $p0
    local.get $p1
    i64.store offset=16
    local.get $p0
    local.get $l6
    i64.store
    local.get $p0
    i32.const 24
    i32.add
    local.get $l11
    i64.store
    local.get $p0
    local.get $l12
    i64.store offset=8
    local.get $l5
    i32.const 32
    i32.add
    global.set $__stack_pointer)
  (func $__divti3 (type $t13) (param $p0 i32) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64)
    (local $l5 i32) (local $l6 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l5
    global.set $__stack_pointer
    local.get $l5
    i64.const 0
    local.get $p1
    i64.sub
    local.get $p1
    local.get $p2
    i64.const 0
    i64.lt_s
    local.tee $l6
    select
    i64.const 0
    local.get $p2
    local.get $p1
    i64.const 0
    i64.ne
    i64.extend_i32_u
    i64.add
    i64.sub
    local.get $p2
    local.get $l6
    select
    i64.const 0
    local.get $p3
    i64.sub
    local.get $p3
    local.get $p4
    i64.const 0
    i64.lt_s
    local.tee $l6
    select
    i64.const 0
    local.get $p4
    local.get $p3
    i64.const 0
    i64.ne
    i64.extend_i32_u
    i64.add
    i64.sub
    local.get $p4
    local.get $l6
    select
    call $_ZN17compiler_builtins3int19specialized_div_rem12u128_div_rem17h037f7f51afb6bf78E
    local.get $l5
    i32.const 8
    i32.add
    i64.load
    local.set $p3
    local.get $p0
    i64.const 0
    local.get $l5
    i64.load
    local.tee $p1
    i64.sub
    local.get $p1
    local.get $p4
    local.get $p2
    i64.xor
    i64.const 0
    i64.lt_s
    local.tee $l6
    select
    i64.store
    local.get $p0
    i64.const 0
    local.get $p3
    local.get $p1
    i64.const 0
    i64.ne
    i64.extend_i32_u
    i64.add
    i64.sub
    local.get $p3
    local.get $l6
    select
    i64.store offset=8
    local.get $l5
    i32.const 32
    i32.add
    global.set $__stack_pointer)
  (func $__ashlti3 (type $t14) (param $p0 i32) (param $p1 i64) (param $p2 i64) (param $p3 i32)
    (local $l4 i64)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p3
        i32.const 64
        i32.and
        br_if 0 (;@2;)
        local.get $p3
        i32.eqz
        br_if 1 (;@1;)
        local.get $p2
        local.get $p3
        i32.const 63
        i32.and
        i64.extend_i32_u
        local.tee $l4
        i64.shl
        local.get $p1
        i32.const 0
        local.get $p3
        i32.sub
        i32.const 63
        i32.and
        i64.extend_i32_u
        i64.shr_u
        i64.or
        local.set $p2
        local.get $p1
        local.get $l4
        i64.shl
        local.set $p1
        br 1 (;@1;)
      end
      local.get $p1
      local.get $p3
      i32.const 63
      i32.and
      i64.extend_i32_u
      i64.shl
      local.set $p2
      i64.const 0
      local.set $p1
    end
    local.get $p0
    local.get $p1
    i64.store
    local.get $p0
    local.get $p2
    i64.store offset=8)
  (func $__multi3 (type $t13) (param $p0 i32) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64)
    (local $l5 i64) (local $l6 i64) (local $l7 i64) (local $l8 i64) (local $l9 i64) (local $l10 i64)
    local.get $p0
    local.get $p3
    i64.const 4294967295
    i64.and
    local.tee $l5
    local.get $p1
    i64.const 4294967295
    i64.and
    local.tee $l6
    i64.mul
    local.tee $l7
    local.get $p3
    i64.const 32
    i64.shr_u
    local.tee $l8
    local.get $l6
    i64.mul
    local.tee $l6
    local.get $l5
    local.get $p1
    i64.const 32
    i64.shr_u
    local.tee $l9
    i64.mul
    i64.add
    local.tee $l5
    i64.const 32
    i64.shl
    i64.add
    local.tee $l10
    i64.store
    local.get $p0
    local.get $l8
    local.get $l9
    i64.mul
    local.get $l5
    local.get $l6
    i64.lt_u
    i64.extend_i32_u
    i64.const 32
    i64.shl
    local.get $l5
    i64.const 32
    i64.shr_u
    i64.or
    i64.add
    local.get $l10
    local.get $l7
    i64.lt_u
    i64.extend_i32_u
    i64.add
    local.get $p4
    local.get $p1
    i64.mul
    local.get $p3
    local.get $p2
    i64.mul
    i64.add
    i64.add
    i64.store offset=8)
  (func $__muloti4 (type $t15) (param $p0 i32) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64) (param $p5 i32)
    (local $l6 i32) (local $l7 i64) (local $l8 i64) (local $l9 i32) (local $l10 i32)
    global.get $__stack_pointer
    i32.const 96
    i32.sub
    local.tee $l6
    global.set $__stack_pointer
    i64.const 0
    local.set $l7
    i64.const 0
    local.set $l8
    i32.const 0
    local.set $l9
    block  ;; label = @1
      local.get $p1
      local.get $p2
      i64.or
      i64.eqz
      br_if 0 (;@1;)
      local.get $p3
      local.get $p4
      i64.or
      i64.eqz
      br_if 0 (;@1;)
      i64.const 0
      local.get $p3
      i64.sub
      local.get $p3
      local.get $p4
      i64.const 0
      i64.lt_s
      local.tee $l9
      select
      local.set $l7
      i64.const 0
      local.get $p1
      i64.sub
      local.get $p1
      local.get $p2
      i64.const 0
      i64.lt_s
      local.tee $l10
      select
      local.set $l8
      i64.const 0
      local.get $p4
      local.get $p3
      i64.const 0
      i64.ne
      i64.extend_i32_u
      i64.add
      i64.sub
      local.get $p4
      local.get $l9
      select
      local.set $p3
      local.get $p4
      local.get $p2
      i64.xor
      local.set $p4
      block  ;; label = @2
        block  ;; label = @3
          i64.const 0
          local.get $p2
          local.get $p1
          i64.const 0
          i64.ne
          i64.extend_i32_u
          i64.add
          i64.sub
          local.get $p2
          local.get $l10
          select
          local.tee $p2
          i64.eqz
          br_if 0 (;@3;)
          block  ;; label = @4
            local.get $p3
            i64.eqz
            br_if 0 (;@4;)
            local.get $l6
            i32.const 80
            i32.add
            local.get $l7
            local.get $p3
            local.get $l8
            local.get $p2
            call $__multi3
            local.get $l6
            i32.const 88
            i32.add
            i64.load
            local.set $p1
            i32.const 1
            local.set $l9
            local.get $l6
            i64.load offset=80
            local.set $p2
            br 2 (;@2;)
          end
          local.get $l6
          i32.const 64
          i32.add
          local.get $l8
          i64.const 0
          local.get $l7
          local.get $p3
          call $__multi3
          local.get $l6
          i32.const 48
          i32.add
          local.get $p2
          i64.const 0
          local.get $l7
          local.get $p3
          call $__multi3
          local.get $l6
          i32.const 64
          i32.add
          i32.const 8
          i32.add
          i64.load
          local.tee $p2
          local.get $l6
          i64.load offset=48
          i64.add
          local.tee $p1
          local.get $p2
          i64.lt_u
          local.get $l6
          i32.const 48
          i32.add
          i32.const 8
          i32.add
          i64.load
          i64.const 0
          i64.ne
          i32.or
          local.set $l9
          local.get $l6
          i64.load offset=64
          local.set $p2
          br 1 (;@2;)
        end
        block  ;; label = @3
          local.get $p3
          i64.eqz
          br_if 0 (;@3;)
          local.get $l6
          i32.const 32
          i32.add
          local.get $l7
          i64.const 0
          local.get $l8
          local.get $p2
          call $__multi3
          local.get $l6
          i32.const 16
          i32.add
          local.get $p3
          i64.const 0
          local.get $l8
          local.get $p2
          call $__multi3
          local.get $l6
          i32.const 32
          i32.add
          i32.const 8
          i32.add
          i64.load
          local.tee $p2
          local.get $l6
          i64.load offset=16
          i64.add
          local.tee $p1
          local.get $p2
          i64.lt_u
          local.get $l6
          i32.const 16
          i32.add
          i32.const 8
          i32.add
          i64.load
          i64.const 0
          i64.ne
          i32.or
          local.set $l9
          local.get $l6
          i64.load offset=32
          local.set $p2
          br 1 (;@2;)
        end
        local.get $l6
        local.get $l7
        local.get $p3
        local.get $l8
        local.get $p2
        call $__multi3
        local.get $l6
        i32.const 8
        i32.add
        i64.load
        local.set $p1
        i32.const 0
        local.set $l9
        local.get $l6
        i64.load
        local.set $p2
      end
      i64.const 0
      local.get $p2
      i64.sub
      local.get $p2
      local.get $p4
      i64.const 0
      i64.lt_s
      local.tee $l10
      select
      local.set $l8
      i64.const 0
      local.get $p1
      local.get $p2
      i64.const 0
      i64.ne
      i64.extend_i32_u
      i64.add
      i64.sub
      local.get $p1
      local.get $l10
      select
      local.tee $l7
      local.get $p4
      i64.xor
      i64.const 0
      i64.lt_s
      local.get $l9
      i32.or
      local.set $l9
    end
    local.get $p5
    local.get $l9
    i32.store
    local.get $p0
    local.get $l7
    i64.store offset=8
    local.get $p0
    local.get $l8
    i64.store
    local.get $l6
    i32.const 96
    i32.add
    global.set $__stack_pointer)
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048668))
  (global $__heap_base i32 (i32.const 1048672))
  (export "memory" (memory $memory))
  (export "create" (func $create))
  (export "trade" (func $trade))
  (export "withdraw" (func $withdraw))
  (export "updt_price" (func $updt_price))
  (export "get_offer" (func $get_offer))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (data $.rodata (i32.const 1048576) "Offerbuy_pricebuy_tokensell_pricesell_tokenseller\00\00\00\05\00\10\00\09\00\00\00\0e\00\10\00\09\00\00\00\17\00\10\00\0a\00\00\00!\00\10\00\0a\00\00\00+\00\10\00\06\00\00\00"))
