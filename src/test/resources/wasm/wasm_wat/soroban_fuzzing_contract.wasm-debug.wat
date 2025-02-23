(module $soroban_fuzzing_contract.wasm
  (type $t0 (func (param i32 i32 i32) (result i32)))
  (type $t1 (func (param i32 i32) (result i32)))
  (type $t2 (func (param i64 i64) (result i64)))
  (type $t3 (func (param i64 i64 i64) (result i64)))
  (type $t4 (func (param i64 i64 i64 i64) (result i64)))
  (type $t5 (func (result i64)))
  (type $t6 (func (param i64) (result i64)))
  (type $t7 (func (param i32 i32 i32)))
  (type $t8 (func (param i32 i32) (result i64)))
  (type $t9 (func (param i32 i32 i32 i64)))
  (type $t10 (func (param i64 i64 i64 i64 i64) (result i64)))
  (type $t11 (func (param i64 i64 i64 i64 i64 i64 i32)))
  (type $t12 (func (param i64 i64 i64)))
  (type $t13 (func (param i32 i64)))
  (type $t14 (func (param i32 i32)))
  (type $t15 (func (param i32) (result i32)))
  (type $t16 (func (param i32)))
  (type $t17 (func))
  (type $t18 (func (param i32) (result i64)))
  (type $t19 (func (param i32 i32 i32 i32 i32) (result i64)))
  (type $t20 (func (param i32 i64 i32 i32 i32 i32) (result i64)))
  (type $t21 (func (param i32 i32 i32) (result i64)))
  (type $t22 (func (param i32 i64 i32 i32) (result i64)))
  (type $t23 (func (param i32 i64 i64) (result i32)))
  (type $t24 (func (param i32 i64 i64) (result i64)))
  (type $t25 (func (param i32 i64) (result i64)))
  (type $t26 (func (param i32 i64 i64 i64) (result i64)))
  (type $t27 (func (param i32 i32 i32 i32)))
  (type $t28 (func (param i64) (result i32)))
  (type $t29 (func (param i32 i64 i64)))
  (type $t30 (func (param i32 i32 i32 i32 i32)))
  (type $t31 (func (param i32 i32 i32 i32 i32 i32) (result i32)))
  (type $t32 (func (param i32 i32 i32 i32 i32) (result i32)))
  (type $t33 (func (param i64 i32 i32) (result i32)))
  (import "b" "j" (func $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17hb02212a3b885b74aE (type $t2)))
  (import "m" "9" (func $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17h1462d18b9e5fcf8fE (type $t3)))
  (import "m" "a" (func $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h19ad59f5b947b3cbE (type $t4)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17hfa3fd9016321cb70E (type $t2)))
  (import "b" "m" (func $_ZN17soroban_env_guest5guest3buf29symbol_index_in_linear_memory17hdc10fd4d66dd77abE (type $t3)))
  (import "x" "4" (func $_ZN17soroban_env_guest5guest7context20get_ledger_timestamp17h3dc89e3bc346e730E (type $t5)))
  (import "x" "7" (func $_ZN17soroban_env_guest5guest7context28get_current_contract_address17hd1d4b7bd620a8a13E (type $t5)))
  (import "i" "_" (func $_ZN17soroban_env_guest5guest3int12obj_from_u6417hf31ac87e20c7a2a1E (type $t6)))
  (import "i" "0" (func $_ZN17soroban_env_guest5guest3int10obj_to_u6417h6dd63be303104bf7E (type $t6)))
  (import "i" "6" (func $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17hae61d1b41bca5c92E (type $t2)))
  (import "i" "7" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_lo6417h473c1689f5477a10E (type $t6)))
  (import "i" "8" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_hi6417h4ad1bb58684df7baE (type $t6)))
  (import "v" "1" (func $_ZN17soroban_env_guest5guest3vec7vec_get17hed53bd0a40d2a5edE (type $t2)))
  (import "v" "3" (func $_ZN17soroban_env_guest5guest3vec7vec_len17h8a9fdafaf3b67c35E (type $t6)))
  (import "v" "d" (func $_ZN17soroban_env_guest5guest3vec18vec_first_index_of17h949a075abe17b538E (type $t2)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h8ee4847deecad99bE (type $t3)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17h8a7244d88b2a25e5E (type $t2)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17hb1d6d2751ce51aa8E (type $t2)))
  (import "l" "2" (func $_ZN17soroban_env_guest5guest6ledger17del_contract_data17hf8d1baf5f895892dE (type $t2)))
  (import "d" "_" (func $_ZN17soroban_env_guest5guest4call4call17hbbe7ab5a2ad81809E (type $t3)))
  (import "a" "0" (func $_ZN17soroban_env_guest5guest7address12require_auth17h3cca0ad538f0fd30E (type $t6)))
  (func $_ZN155_$LT$soroban_fuzzing_contract..TimeBound$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0449dd0e0fb24385E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i32) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    i32.const 0
    local.set $l4
    block  ;; label = @1
      loop  ;; label = @2
        local.get $l4
        i32.const 16
        i32.eq
        br_if 1 (;@1;)
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
        br 0 (;@2;)
      end
    end
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p2
          i64.load
          local.tee $l5
          i64.const 255
          i64.and
          i64.const 76
          i64.ne
          br_if 0 (;@3;)
          i32.const 2
          local.set $l4
          local.get $p1
          local.get $l5
          i32.const 1048680
          i32.const 2
          local.get $l3
          i32.const 16
          i32.add
          i32.const 2
          call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17he2c6fd8b8e43f65aE
          drop
          local.get $l3
          i32.const 16
          i32.add
          local.get $p1
          call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hc04111b565fb5614E
          local.tee $p2
          i32.const 255
          i32.and
          i32.const 2
          i32.eq
          br_if 1 (;@2;)
          local.get $l3
          local.get $p1
          local.get $l3
          i32.const 24
          i32.add
          call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hb0432fd2b1fc61e7E
          local.get $l3
          i64.load
          i32.wrap_i64
          br_if 0 (;@3;)
          local.get $p2
          i32.const 1
          i32.and
          local.set $l4
          local.get $l3
          i64.load offset=8
          local.set $l5
          br 2 (;@1;)
        end
        i32.const 2
        local.set $l4
      end
    end
    local.get $p0
    local.get $l4
    i32.store8 offset=8
    local.get $p0
    local.get $l5
    i64.store
    local.get $l3
    i32.const 32
    i32.add
    global.set $__stack_pointer)
  (func $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h3f3d24b3b6b93598E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $p1
    local.get $p2
    call $_ZN106_$LT$soroban_env_common..num..U64Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h8018eaa625085521E
    local.get $p0
    local.get $l3
    i64.load offset=8
    i64.store offset=8
    local.get $p0
    i64.const 0
    i64.store
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN106_$LT$soroban_env_common..num..U64Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h8018eaa625085521E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $p2
    i64.load
    local.tee $l4
    call $_ZN87_$LT$soroban_env_common..num..U64Small$u20$as$u20$core..convert..TryFrom$LT$u64$GT$$GT$8try_from17h42d186eeb2ac18e2E
    block  ;; label = @1
      block  ;; label = @2
        local.get $l3
        i64.load
        i32.wrap_i64
        br_if 0 (;@2;)
        local.get $l3
        i64.load offset=8
        local.set $l4
        br 1 (;@1;)
      end
      local.get $p1
      local.get $l4
      call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$12obj_from_u6417hfec479798a3b31dcE
      local.set $l4
    end
    local.get $p0
    local.get $l4
    i64.store offset=8
    local.get $p0
    i64.const 0
    i64.store
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hb0432fd2b1fc61e7E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i64) (local $l4 i64)
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p2
          i64.load
          local.tee $l3
          i32.wrap_i64
          i32.const 255
          i32.and
          local.tee $p2
          i32.const 64
          i32.eq
          br_if 0 (;@3;)
          local.get $p2
          i32.const 6
          i32.ne
          br_if 1 (;@2;)
          i64.const 0
          local.set $l4
          local.get $l3
          call $_ZN101_$LT$soroban_env_common..symbol..SymbolSmall$u20$as$u20$core..iter..traits..collect..IntoIterator$GT$9into_iter17h96cb636c76edde29E
          local.set $l3
          br 2 (;@1;)
        end
        i64.const 0
        local.set $l4
        local.get $p1
        local.get $l3
        call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$10obj_to_u6417hb85eb8f9dd45bf0aE
        local.set $l3
        br 1 (;@1;)
      end
      i64.const 1
      local.set $l4
      call $_ZN120_$LT$soroban_env_common..error..Error$u20$as$u20$core..convert..From$LT$soroban_env_common..val..ConversionError$GT$$GT$4from17h830fb10c420e09b3E
      local.set $l3
    end
    local.get $p0
    local.get $l3
    i64.store offset=8
    local.get $p0
    local.get $l4
    i64.store)
  (func $_ZN11soroban_sdk7storage10Persistent3get17h2392e01018de3200E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 64
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p1
          local.get $p1
          local.get $p2
          call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..FromVal$LT$E$C$T$GT$$GT$8from_val17hb392e862f86da753E
          local.tee $l4
          i64.const 1
          call $_ZN11soroban_sdk7storage7Storage12has_internal17h76da7d30a596b93aE
          br_if 0 (;@3;)
          local.get $p0
          i32.const 2
          i32.store8 offset=40
          br 1 (;@2;)
        end
        local.get $l3
        local.get $p1
        local.get $l4
        i64.const 1
        call $_ZN11soroban_sdk7storage7Storage12get_internal17h0c3bb0d738b8e739E
        i64.store offset=8
        local.get $l3
        i32.const 16
        i32.add
        local.get $p1
        local.get $l3
        i32.const 8
        i32.add
        call $_ZN162_$LT$soroban_fuzzing_contract..ClaimableBalance$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h41bf645ac3fd4ac3E
        local.get $l3
        i32.load8_u offset=56
        i32.const 2
        i32.eq
        br_if 1 (;@1;)
        local.get $p0
        local.get $l3
        i32.const 16
        i32.add
        i32.const 48
        call $memcpy
        drop
      end
      local.get $l3
      i32.const 64
      i32.add
      global.set $__stack_pointer
      return
    end
    unreachable
    unreachable)
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..FromVal$LT$E$C$T$GT$$GT$8from_val17hb392e862f86da753E (type $t8) (param $p0 i32) (param $p1 i32) (result i64)
    (local $l2 i32) (local $l3 i64) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 80
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            local.get $p1
            i32.load8_u
            br_if 0 (;@4;)
            local.get $l2
            i32.const 16
            i32.add
            local.get $p0
            i32.const 1048584
            call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h941971ca3e19786fE
            local.get $l2
            i64.load offset=16
            i32.wrap_i64
            br_if 2 (;@2;)
            local.get $l2
            local.get $l2
            i64.load offset=24
            i64.store offset=72
            local.get $l2
            local.get $l2
            i32.const 72
            i32.add
            call $_ZN11soroban_sdk3num4I2566to_val17ha5879f16a4e765c3E
            i64.store offset=64
            local.get $l2
            local.get $p0
            local.get $l2
            i32.const 64
            i32.add
            call $_ZN18soroban_env_common5tuple123_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$LP$T0$C$$RP$$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17heead6e1db404908dE
            local.get $l2
            i64.load offset=8
            local.set $l3
            local.get $l2
            i64.load
            local.set $l4
            br 1 (;@3;)
          end
          local.get $l2
          i32.const 48
          i32.add
          local.get $p0
          i32.const 1048612
          call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h941971ca3e19786fE
          local.get $l2
          i64.load offset=48
          i32.wrap_i64
          br_if 1 (;@2;)
          local.get $l2
          local.get $l2
          i64.load offset=56
          i64.store offset=72
          local.get $l2
          local.get $l2
          i32.const 72
          i32.add
          call $_ZN11soroban_sdk3num4I2566to_val17ha5879f16a4e765c3E
          i64.store offset=64
          local.get $l2
          i32.const 32
          i32.add
          local.get $p0
          local.get $l2
          i32.const 64
          i32.add
          call $_ZN18soroban_env_common5tuple123_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$LP$T0$C$$RP$$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17heead6e1db404908dE
          local.get $l2
          i64.load offset=40
          local.set $l3
          local.get $l2
          i64.load offset=32
          local.set $l4
        end
        local.get $l4
        i32.wrap_i64
        i32.eqz
        br_if 1 (;@1;)
      end
      unreachable
      unreachable
    end
    local.get $l2
    i32.const 80
    i32.add
    global.set $__stack_pointer
    local.get $l3)
  (func $_ZN162_$LT$soroban_fuzzing_contract..ClaimableBalance$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h41bf645ac3fd4ac3E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i32) (local $l5 i64) (local $l6 i64) (local $l7 i64) (local $l8 i64) (local $l9 i64)
    global.get $__stack_pointer
    i32.const 96
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    i32.const 0
    local.set $l4
    block  ;; label = @1
      loop  ;; label = @2
        local.get $l4
        i32.const 32
        i32.eq
        br_if 1 (;@1;)
        local.get $l3
        i32.const 40
        i32.add
        local.get $l4
        i32.add
        i64.const 2
        i64.store
        local.get $l4
        i32.const 8
        i32.add
        local.set $l4
        br 0 (;@2;)
      end
    end
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              local.get $p2
              i64.load
              local.tee $l5
              i64.const 255
              i64.and
              i64.const 76
              i64.ne
              br_if 0 (;@5;)
              local.get $p1
              local.get $l5
              i32.const 1048728
              i32.const 4
              local.get $l3
              i32.const 40
              i32.add
              i32.const 4
              call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17he2c6fd8b8e43f65aE
              drop
              local.get $l3
              i32.const 72
              i32.add
              local.get $p1
              local.get $l3
              i32.const 40
              i32.add
              call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h60a56e891f88b6daE
              local.get $l3
              i64.load offset=72
              i64.eqz
              i32.eqz
              br_if 1 (;@4;)
              local.get $l3
              i64.load offset=48
              local.tee $l5
              i64.const 255
              i64.and
              i64.const 75
              i64.ne
              br_if 2 (;@3;)
              local.get $l3
              i32.const 88
              i32.add
              i64.load
              local.set $l6
              local.get $l3
              i64.load offset=80
              local.set $l7
              local.get $l3
              i32.const 24
              i32.add
              local.get $p1
              local.get $l3
              i32.const 56
              i32.add
              call $_ZN155_$LT$soroban_fuzzing_contract..TimeBound$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0449dd0e0fb24385E
              local.get $l3
              i32.load8_u offset=32
              local.tee $l4
              i32.const 2
              i32.eq
              br_if 3 (;@2;)
              local.get $l3
              i64.load offset=24
              local.set $l8
              local.get $l3
              i32.const 8
              i32.add
              local.get $l3
              i32.const 64
              i32.add
              local.get $p1
              call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h5ae9c792ed9ddb0aE
              block  ;; label = @6
                local.get $l3
                i64.load offset=8
                i32.wrap_i64
                br_if 0 (;@6;)
                local.get $l3
                i64.load offset=16
                local.set $l9
                local.get $p0
                local.get $l7
                i64.store
                local.get $p0
                local.get $l4
                i32.const 1
                i32.and
                i32.store8 offset=40
                local.get $p0
                local.get $l8
                i64.store offset=32
                local.get $p0
                local.get $l5
                i64.store offset=24
                local.get $p0
                local.get $l6
                i64.store offset=8
                local.get $p0
                local.get $l9
                i64.store offset=16
                br 5 (;@1;)
              end
              local.get $p0
              i32.const 2
              i32.store8 offset=40
              br 4 (;@1;)
            end
            local.get $p0
            i32.const 2
            i32.store8 offset=40
            br 3 (;@1;)
          end
          local.get $p0
          i32.const 2
          i32.store8 offset=40
          br 2 (;@1;)
        end
        local.get $p0
        i32.const 2
        i32.store8 offset=40
        br 1 (;@1;)
      end
      local.get $p0
      i32.const 2
      i32.store8 offset=40
    end
    local.get $l3
    i32.const 96
    i32.add
    global.set $__stack_pointer)
  (func $_ZN11soroban_sdk7storage10Persistent3has17h6d4cab04c518ec44E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p0
    local.get $p0
    local.get $p1
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..FromVal$LT$E$C$T$GT$$GT$8from_val17hb392e862f86da753E
    i64.const 1
    call $_ZN11soroban_sdk7storage7Storage12has_internal17h76da7d30a596b93aE)
  (func $_ZN11soroban_sdk7storage10Persistent3set17h93f9c8aa4416532dE (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    local.get $p0
    local.get $p1
    local.get $p2
    i64.const 1
    call $_ZN11soroban_sdk7storage7Storage3set17h442d8bbb29c88870E)
  (func $_ZN11soroban_sdk7storage7Storage3set17h442d8bbb29c88870E (type $t9) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i64)
    local.get $p0
    local.get $p0
    local.get $p1
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..FromVal$LT$E$C$T$GT$$GT$8from_val17hb392e862f86da753E
    local.get $p0
    local.get $p2
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..FromVal$LT$E$C$T$GT$$GT$8from_val17hdfa40acc324df9c5E
    local.get $p3
    call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$17put_contract_data17hdee22151560b1714E
    drop)
  (func $_ZN11soroban_sdk7storage10Persistent3set17he0405f0bb2f95a8bE (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    local.get $p0
    local.get $p1
    local.get $p1
    i64.const 1
    call $_ZN11soroban_sdk7storage7Storage3set17h2cf13179c10dd75eE)
  (func $_ZN11soroban_sdk7storage7Storage3set17h2cf13179c10dd75eE (type $t9) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i64)
    local.get $p0
    local.get $p0
    local.get $p1
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..FromVal$LT$E$C$T$GT$$GT$8from_val17hb392e862f86da753E
    i64.const 2
    local.get $p3
    call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$17put_contract_data17hdee22151560b1714E
    drop)
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..FromVal$LT$E$C$T$GT$$GT$8from_val17hdfa40acc324df9c5E (type $t8) (param $p0 i32) (param $p1 i32) (result i64)
    (local $l2 i32) (local $l3 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    local.get $p0
    local.get $p1
    call $_ZN24soroban_fuzzing_contract172_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_fuzzing_contract..ClaimableBalance$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17he3f1a6baf29beb7aE
    block  ;; label = @1
      local.get $l2
      i64.load
      i32.wrap_i64
      i32.eqz
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $l2
    i64.load offset=8
    local.set $l3
    local.get $l2
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l3)
  (func $_ZN18soroban_env_common5tuple123_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$LP$T0$C$$RP$$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17heead6e1db404908dE (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    i32.const 8
    i32.add
    local.get $p2
    local.get $p1
    call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hcddf0191ee673ce5E
    block  ;; label = @1
      block  ;; label = @2
        local.get $l3
        i64.load offset=8
        i32.wrap_i64
        br_if 0 (;@2;)
        local.get $l3
        local.get $l3
        i64.load offset=16
        i64.store offset=24
        local.get $p1
        local.get $l3
        i32.const 24
        i32.add
        i32.const 1
        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hc5c8d35ed2002e9bE
        local.set $l4
        i64.const 0
        local.set $l5
        br 1 (;@1;)
      end
      call $_ZN120_$LT$soroban_env_common..error..Error$u20$as$u20$core..convert..From$LT$soroban_env_common..val..ConversionError$GT$$GT$4from17h830fb10c420e09b3E
      local.set $l4
      i64.const 1
      local.set $l5
    end
    local.get $p0
    local.get $l4
    i64.store offset=8
    local.get $p0
    local.get $l5
    i64.store
    local.get $l3
    i32.const 32
    i32.add
    global.set $__stack_pointer)
  (func $_ZN24soroban_fuzzing_contract165_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_fuzzing_contract..TimeBound$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17hb4ff26c37a02504bE (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    i32.const 16
    i32.add
    local.get $p2
    i32.const 8
    i32.add
    local.get $p1
    call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hacf275810efb79fbE
    block  ;; label = @1
      block  ;; label = @2
        local.get $l3
        i64.load offset=16
        i32.wrap_i64
        br_if 0 (;@2;)
        local.get $l3
        i64.load offset=24
        local.set $l4
        local.get $l3
        local.get $p1
        local.get $p2
        call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h3f3d24b3b6b93598E
        local.get $l3
        local.get $l4
        i64.store offset=32
        local.get $l3
        local.get $l3
        i64.load offset=8
        i64.store offset=40
        local.get $p1
        i32.const 1048680
        i32.const 2
        local.get $l3
        i32.const 32
        i32.add
        i32.const 2
        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h46c1f0b4bb90c3afE
        local.set $l4
        i64.const 0
        local.set $l5
        br 1 (;@1;)
      end
      i64.const 1
      local.set $l5
    end
    local.get $p0
    local.get $l4
    i64.store offset=8
    local.get $p0
    local.get $l5
    i64.store
    local.get $l3
    i32.const 48
    i32.add
    global.set $__stack_pointer)
  (func $_ZN24soroban_fuzzing_contract172_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_fuzzing_contract..ClaimableBalance$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17he3f1a6baf29beb7aE (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64) (local $l5 i64) (local $l6 i64) (local $l7 i64)
    global.get $__stack_pointer
    i32.const 80
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    i32.const 32
    i32.add
    local.get $p1
    local.get $p2
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h2c8d473123972f3dE
    block  ;; label = @1
      block  ;; label = @2
        local.get $l3
        i32.load offset=32
        br_if 0 (;@2;)
        local.get $l3
        i64.load offset=40
        local.set $l4
        local.get $p2
        i64.load offset=24
        local.set $l5
        local.get $l3
        i32.const 16
        i32.add
        local.get $p1
        local.get $p2
        i32.const 32
        i32.add
        call $_ZN24soroban_fuzzing_contract165_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_fuzzing_contract..TimeBound$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17hb4ff26c37a02504bE
        local.get $l3
        i32.load offset=16
        br_if 0 (;@2;)
        local.get $l3
        i64.load offset=24
        local.set $l6
        local.get $l3
        local.get $p2
        i32.const 16
        i32.add
        local.get $p1
        call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h0b335473af49db75E
        local.get $l3
        i64.load
        i32.wrap_i64
        br_if 0 (;@2;)
        local.get $l3
        i64.load offset=8
        local.set $l7
        local.get $l3
        local.get $l6
        i64.store offset=64
        local.get $l3
        local.get $l5
        i64.store offset=56
        local.get $l3
        local.get $l4
        i64.store offset=48
        local.get $l3
        local.get $l7
        i64.store offset=72
        local.get $p1
        i32.const 1048728
        i32.const 4
        local.get $l3
        i32.const 48
        i32.add
        i32.const 4
        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h46c1f0b4bb90c3afE
        local.set $l4
        i64.const 0
        local.set $l5
        br 1 (;@1;)
      end
      i64.const 1
      local.set $l5
    end
    local.get $p0
    local.get $l4
    i64.store offset=8
    local.get $p0
    local.get $l5
    i64.store
    local.get $l3
    i32.const 80
    i32.add
    global.set $__stack_pointer)
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hacf275810efb79fbE (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 80
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            local.get $p1
            i32.load8_u
            br_if 0 (;@4;)
            local.get $l3
            i32.const 16
            i32.add
            local.get $p2
            i32.const 1048648
            call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h941971ca3e19786fE
            local.get $l3
            i64.load offset=16
            i32.wrap_i64
            br_if 1 (;@3;)
            local.get $l3
            local.get $l3
            i64.load offset=24
            i64.store offset=72
            local.get $l3
            local.get $l3
            i32.const 72
            i32.add
            call $_ZN11soroban_sdk3num4I2566to_val17ha5879f16a4e765c3E
            i64.store offset=64
            local.get $l3
            local.get $p2
            local.get $l3
            i32.const 64
            i32.add
            call $_ZN18soroban_env_common5tuple123_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$LP$T0$C$$RP$$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17heead6e1db404908dE
            local.get $l3
            i32.load
            i32.const 0
            i32.ne
            local.set $p2
            local.get $l3
            i64.load offset=8
            local.set $l4
            br 3 (;@1;)
          end
          local.get $l3
          i32.const 48
          i32.add
          local.get $p2
          i32.const 1048656
          call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h941971ca3e19786fE
          local.get $l3
          i64.load offset=48
          i32.wrap_i64
          i32.eqz
          br_if 1 (;@2;)
        end
        i32.const 1
        local.set $p2
        br 1 (;@1;)
      end
      local.get $l3
      local.get $l3
      i64.load offset=56
      i64.store offset=72
      local.get $l3
      local.get $l3
      i32.const 72
      i32.add
      call $_ZN11soroban_sdk3num4I2566to_val17ha5879f16a4e765c3E
      i64.store offset=64
      local.get $l3
      i32.const 32
      i32.add
      local.get $p2
      local.get $l3
      i32.const 64
      i32.add
      call $_ZN18soroban_env_common5tuple123_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$LP$T0$C$$RP$$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17heead6e1db404908dE
      local.get $l3
      i32.load offset=32
      i32.const 0
      i32.ne
      local.set $p2
      local.get $l3
      i64.load offset=40
      local.set $l4
    end
    local.get $p0
    local.get $l4
    i64.store offset=8
    local.get $p0
    local.get $p2
    i64.extend_i32_u
    i64.store
    local.get $l3
    i32.const 80
    i32.add
    global.set $__stack_pointer)
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hc04111b565fb5614E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32)
    global.get $__stack_pointer
    i32.const 80
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    i32.const 32
    i32.add
    local.get $p0
    local.get $p1
    call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h20bfac56f373f0fbE
    block  ;; label = @1
      block  ;; label = @2
        local.get $l2
        i64.load offset=32
        i32.wrap_i64
        br_if 0 (;@2;)
        local.get $l2
        local.get $l2
        i64.load offset=40
        i64.store offset=48
        local.get $l2
        i32.const 56
        i32.add
        local.get $l2
        i32.const 48
        i32.add
        call $_ZN69_$LT$soroban_sdk..vec..Vec$LT$T$GT$$u20$as$u20$core..clone..Clone$GT$5clone17h7ebc08ea59ba3b99E
        call $_ZN11soroban_sdk3vec19VecTryIter$LT$T$GT$3new17hf032d0bf5104dcdbE
        local.get $l2
        i32.const 16
        i32.add
        local.get $l2
        i32.const 56
        i32.add
        call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hb9b532c12128b442E
        local.get $l2
        i64.load offset=16
        i32.wrap_i64
        br_if 0 (;@2;)
        local.get $l2
        local.get $l2
        i64.load offset=24
        i64.store offset=72
        local.get $l2
        local.get $l2
        i32.const 72
        i32.add
        local.get $p1
        call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hff8c2adbd7f91526E
        local.get $l2
        i64.load
        i32.wrap_i64
        br_if 0 (;@2;)
        i32.const 2
        local.set $p0
        block  ;; label = @3
          block  ;; label = @4
            local.get $p1
            local.get $l2
            i64.load offset=8
            i32.const 1048632
            i32.const 2
            call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$20symbol_index_in_strs17hb337be2c8bdc7236E
            call $_ZN18soroban_env_common3num92_$LT$impl$u20$core..convert..From$LT$soroban_env_common..num..I32Val$GT$$u20$for$u20$i32$GT$4from17hfd042b091018bf24E
            br_table 0 (;@4;) 1 (;@3;) 3 (;@1;)
          end
          local.get $l2
          i32.const 56
          i32.add
          call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h52b4cfee374261f2E
          br_if 2 (;@1;)
          i32.const 0
          local.set $p0
          br 2 (;@1;)
        end
        local.get $l2
        i32.const 56
        i32.add
        call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h52b4cfee374261f2E
        br_if 1 (;@1;)
        i32.const 1
        local.set $p0
        br 1 (;@1;)
      end
      i32.const 2
      local.set $p0
    end
    local.get $l2
    i32.const 80
    i32.add
    global.set $__stack_pointer
    local.get $p0)
  (func $deposit (type $t10) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64) (result i64)
    (local $l5 i32) (local $l6 i32)
    global.get $__stack_pointer
    i32.const 112
    i32.sub
    local.tee $l5
    global.set $__stack_pointer
    local.get $l5
    local.get $p1
    i64.store offset=56
    local.get $l5
    local.get $p0
    i64.store offset=48
    local.get $l5
    local.get $p2
    i64.store offset=64
    local.get $l5
    local.get $p4
    i64.store offset=72
    local.get $l5
    i32.const 32
    i32.add
    local.get $l5
    i32.const 111
    i32.add
    local.get $l5
    i32.const 48
    i32.add
    call $_ZN149_$LT$soroban_sdk..address..Address$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h8d74483e028fd698E
    block  ;; label = @1
      local.get $l5
      i64.load offset=32
      i32.wrap_i64
      br_if 0 (;@1;)
      local.get $l5
      i64.load offset=40
      local.set $p1
      local.get $l5
      i32.const 16
      i32.add
      local.get $l5
      i32.const 111
      i32.add
      local.get $l5
      i32.const 56
      i32.add
      call $_ZN149_$LT$soroban_sdk..address..Address$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h8d74483e028fd698E
      local.get $l5
      i64.load offset=16
      i32.wrap_i64
      br_if 0 (;@1;)
      local.get $l5
      i64.load offset=24
      local.set $p0
      local.get $l5
      i32.const 80
      i32.add
      local.get $l5
      i32.const 111
      i32.add
      local.get $l5
      i32.const 64
      i32.add
      call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h60a56e891f88b6daE
      local.get $l5
      i64.load offset=80
      i64.eqz
      i32.eqz
      br_if 0 (;@1;)
      local.get $p3
      i64.const 255
      i64.and
      i64.const 75
      i64.ne
      br_if 0 (;@1;)
      local.get $l5
      i32.const 96
      i32.add
      i64.load
      local.set $p2
      local.get $l5
      i64.load offset=88
      local.set $p4
      local.get $l5
      local.get $l5
      i32.const 111
      i32.add
      local.get $l5
      i32.const 72
      i32.add
      call $_ZN155_$LT$soroban_fuzzing_contract..TimeBound$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0449dd0e0fb24385E
      local.get $l5
      i32.load8_u offset=8
      local.tee $l6
      i32.const 2
      i32.eq
      br_if 0 (;@1;)
      local.get $p1
      local.get $p0
      local.get $p4
      local.get $p2
      local.get $p3
      local.get $l5
      i64.load
      local.get $l6
      i32.const 1
      i32.and
      call $_ZN24soroban_fuzzing_contract24ClaimableBalanceContract7deposit17he797a4dde4fc85b8E
      local.get $l5
      i32.const 112
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    unreachable
    unreachable)
  (func $_ZN24soroban_fuzzing_contract24ClaimableBalanceContract7deposit17he797a4dde4fc85b8E (type $t11) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64) (param $p5 i64) (param $p6 i32)
    (local $l7 i32) (local $l8 i32)
    global.get $__stack_pointer
    i32.const 96
    i32.sub
    local.tee $l7
    global.set $__stack_pointer
    local.get $l7
    local.get $p3
    i64.store offset=24
    local.get $l7
    local.get $p2
    i64.store offset=16
    local.get $l7
    local.get $p1
    i64.store offset=8
    local.get $l7
    local.get $p0
    i64.store
    local.get $l7
    local.get $p4
    i64.store offset=32
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $l7
          i32.const 40
          i32.add
          local.tee $l8
          local.get $p4
          call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$7vec_len17h31d93a0baf23dfbbE
          call $_ZN18soroban_env_common3num92_$LT$impl$u20$core..convert..From$LT$soroban_env_common..num..I32Val$GT$$u20$for$u20$i32$GT$4from17hfd042b091018bf24E
          i32.eqz
          br_if 0 (;@3;)
          local.get $l8
          local.get $l7
          i64.load offset=32
          call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$7vec_len17h31d93a0baf23dfbbE
          call $_ZN18soroban_env_common3num92_$LT$impl$u20$core..convert..From$LT$soroban_env_common..num..I32Val$GT$$u20$for$u20$i32$GT$4from17hfd042b091018bf24E
          i32.const 10
          i32.gt_u
          br_if 1 (;@2;)
          local.get $l7
          i32.const 48
          i32.add
          call $_ZN11soroban_sdk4prng4Prng3new17h80882443cd5683a7E
          local.get $l7
          i32.const 48
          i32.add
          i32.const 1048576
          call $_ZN11soroban_sdk7storage10Persistent3has17h6d4cab04c518ec44E
          i32.eqz
          br_if 2 (;@1;)
          local.get $l7
          i32.const 0
          i32.store offset=64
          local.get $l7
          i32.const 1
          i32.store offset=52
          local.get $l7
          i32.const 1048800
          i32.store offset=48
          local.get $l7
          i64.const 4
          i64.store offset=56 align=4
          local.get $l7
          i32.const 48
          i32.add
          i32.const 1048808
          call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
          unreachable
        end
        local.get $l7
        i32.const 0
        i32.store offset=64
        local.get $l7
        i32.const 1
        i32.store offset=52
        local.get $l7
        i32.const 1048896
        i32.store offset=48
        local.get $l7
        i64.const 4
        i64.store offset=56 align=4
        local.get $l7
        i32.const 48
        i32.add
        i32.const 1048904
        call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
        unreachable
      end
      local.get $l7
      i32.const 0
      i32.store offset=64
      local.get $l7
      i32.const 1
      i32.store offset=52
      local.get $l7
      i32.const 1048844
      i32.store offset=48
      local.get $l7
      i64.const 4
      i64.store offset=56 align=4
      local.get $l7
      i32.const 48
      i32.add
      i32.const 1048852
      call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
      unreachable
    end
    local.get $l7
    call $_ZN11soroban_sdk7address7Address12require_auth17h2b3188645da2623eE
    local.get $l7
    local.get $l7
    i32.const 48
    i32.add
    local.get $l7
    i32.const 8
    i32.add
    call $_ZN11soroban_sdk5token11TokenClient3new17h87e13961d8149299E
    i64.store offset=40
    local.get $l7
    local.get $l7
    i32.const 48
    i32.add
    call $_ZN11soroban_sdk3env3Env24current_contract_address17h8e55331aeccd768aE
    i64.store offset=48
    local.get $l7
    i32.const 40
    i32.add
    local.get $l7
    local.get $l7
    i32.const 48
    i32.add
    local.get $l7
    i32.const 16
    i32.add
    call $_ZN11soroban_sdk5token11TokenClient8transfer17h3a967ba5161c1b0dE
    local.get $l7
    i32.const 48
    i32.add
    call $_ZN11soroban_sdk4prng4Prng3new17h80882443cd5683a7E
    local.get $l7
    local.get $l7
    i32.const 24
    i32.add
    i64.load
    i64.store offset=56
    local.get $l7
    local.get $l7
    i64.load offset=16
    i64.store offset=48
    local.get $l7
    local.get $l7
    i64.load offset=8
    i64.store offset=64
    local.get $l7
    local.get $p6
    i32.store8 offset=88
    local.get $l7
    local.get $p5
    i64.store offset=80
    local.get $l7
    local.get $l7
    i64.load offset=32
    i64.store offset=72
    local.get $l7
    i32.const 48
    i32.add
    i32.const 1048760
    local.get $l7
    i32.const 48
    i32.add
    call $_ZN11soroban_sdk7storage10Persistent3set17h93f9c8aa4416532dE
    local.get $l7
    i32.const 48
    i32.add
    call $_ZN11soroban_sdk4prng4Prng3new17h80882443cd5683a7E
    local.get $l7
    i32.const 48
    i32.add
    i32.const 1048576
    i32.const 1
    call $_ZN11soroban_sdk7storage10Persistent3set17he0405f0bb2f95a8bE
    local.get $l7
    i32.const 96
    i32.add
    global.set $__stack_pointer)
  (func $claim (type $t2) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32)
    global.get $__stack_pointer
    i32.const 64
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    local.get $p1
    i64.store offset=24
    local.get $l2
    local.get $p0
    i64.store offset=16
    local.get $l2
    local.get $l2
    i32.const 63
    i32.add
    local.get $l2
    i32.const 16
    i32.add
    call $_ZN149_$LT$soroban_sdk..address..Address$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h8d74483e028fd698E
    block  ;; label = @1
      local.get $l2
      i64.load
      i32.wrap_i64
      br_if 0 (;@1;)
      local.get $l2
      i64.load offset=8
      local.set $p1
      local.get $l2
      i32.const 32
      i32.add
      local.get $l2
      i32.const 63
      i32.add
      local.get $l2
      i32.const 24
      i32.add
      call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h60a56e891f88b6daE
      local.get $l2
      i64.load offset=32
      i64.eqz
      i32.eqz
      br_if 0 (;@1;)
      local.get $p1
      local.get $l2
      i64.load offset=40
      local.get $l2
      i32.const 48
      i32.add
      i64.load
      call $_ZN24soroban_fuzzing_contract24ClaimableBalanceContract5claim17h54b07fa1d5445817E
      local.get $l2
      i32.const 64
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    unreachable
    unreachable)
  (func $_ZN24soroban_fuzzing_contract24ClaimableBalanceContract5claim17h54b07fa1d5445817E (type $t12) (param $p0 i64) (param $p1 i64) (param $p2 i64)
    (local $l3 i32) (local $l4 i64) (local $l5 i32)
    global.get $__stack_pointer
    i32.const 128
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $p2
    i64.store offset=16
    local.get $l3
    local.get $p1
    i64.store offset=8
    local.get $l3
    local.get $p0
    i64.store
    local.get $l3
    call $_ZN11soroban_sdk7address7Address12require_auth17h2b3188645da2623eE
    local.get $l3
    i32.const 72
    i32.add
    call $_ZN11soroban_sdk4prng4Prng3new17h80882443cd5683a7E
    local.get $l3
    i32.const 72
    i32.add
    local.get $l3
    i32.const 72
    i32.add
    i32.const 1048760
    call $_ZN11soroban_sdk7storage10Persistent3get17h2392e01018de3200E
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              local.get $l3
              i32.load8_u offset=112
              i32.const 2
              i32.eq
              br_if 0 (;@5;)
              local.get $l3
              i32.const 24
              i32.add
              local.get $l3
              i32.const 72
              i32.add
              i32.const 48
              call $memcpy
              drop
              local.get $l3
              i32.const 72
              i32.add
              call $_ZN11soroban_sdk6ledger6Ledger9timestamp17h482cdd452385aa10E
              local.tee $p0
              local.get $l3
              i64.load offset=56
              local.tee $l4
              i64.ge_u
              local.get $p0
              local.get $l4
              i64.le_u
              local.get $l3
              i32.load8_u offset=64
              select
              i32.eqz
              br_if 1 (;@4;)
              local.get $l3
              local.get $l3
              i32.const 56
              i32.add
              local.tee $l5
              call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hc8b691dc1c6bcc69E
              local.set $p0
              local.get $l5
              local.get $l3
              i64.load offset=48
              local.get $p0
              call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$18vec_first_index_of17h92d165a34b0e6360E
              i64.const 2
              i64.eq
              br_if 2 (;@3;)
              local.get $l3
              i64.load offset=24
              local.get $p1
              i64.lt_u
              local.get $l3
              i32.const 32
              i32.add
              local.tee $l5
              i64.load
              local.tee $p0
              local.get $p2
              i64.lt_s
              local.get $p0
              local.get $p2
              i64.eq
              select
              br_if 3 (;@2;)
              local.get $l3
              local.get $l3
              i32.const 72
              i32.add
              local.get $l3
              i32.const 40
              i32.add
              call $_ZN11soroban_sdk5token11TokenClient3new17h87e13961d8149299E
              i64.store offset=120
              local.get $l3
              local.get $l3
              i32.const 72
              i32.add
              call $_ZN11soroban_sdk3env3Env24current_contract_address17h8e55331aeccd768aE
              i64.store offset=72
              local.get $l3
              i32.const 120
              i32.add
              local.get $l3
              i32.const 72
              i32.add
              local.get $l3
              local.get $l3
              i32.const 8
              i32.add
              call $_ZN11soroban_sdk5token11TokenClient8transfer17h3a967ba5161c1b0dE
              local.get $l5
              i64.load
              local.tee $p0
              local.get $p2
              i64.xor
              local.get $p0
              local.get $p0
              local.get $p2
              i64.sub
              local.get $l3
              i64.load offset=24
              local.tee $l4
              local.get $p1
              i64.lt_u
              i64.extend_i32_u
              i64.sub
              local.tee $p2
              i64.xor
              i64.and
              i64.const 0
              i64.lt_s
              br_if 4 (;@1;)
              block  ;; label = @6
                block  ;; label = @7
                  local.get $l4
                  local.get $p1
                  i64.sub
                  local.tee $p1
                  i64.const 0
                  i64.ne
                  local.get $p2
                  i64.const 0
                  i64.gt_s
                  local.get $p2
                  i64.eqz
                  select
                  br_if 0 (;@7;)
                  local.get $l3
                  i32.const 72
                  i32.add
                  call $_ZN11soroban_sdk4prng4Prng3new17h80882443cd5683a7E
                  local.get $l3
                  i32.const 72
                  i32.add
                  local.get $l3
                  i32.const 72
                  i32.add
                  i32.const 1048760
                  call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..FromVal$LT$E$C$T$GT$$GT$8from_val17hb392e862f86da753E
                  i64.const 1
                  call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$17del_contract_data17h9b108e7191bde848E
                  drop
                  br 1 (;@6;)
                end
                local.get $l3
                local.get $p1
                i64.store offset=24
                local.get $l3
                local.get $p2
                i64.store offset=32
                local.get $l3
                i32.const 72
                i32.add
                call $_ZN11soroban_sdk4prng4Prng3new17h80882443cd5683a7E
                local.get $l3
                i32.const 72
                i32.add
                i32.const 1048760
                local.get $l3
                i32.const 24
                i32.add
                call $_ZN11soroban_sdk7storage10Persistent3set17h93f9c8aa4416532dE
              end
              local.get $l3
              i32.const 128
              i32.add
              global.set $__stack_pointer
              return
            end
            i32.const 1048920
            call $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E
            unreachable
          end
          local.get $l3
          i32.const 0
          i32.store offset=88
          local.get $l3
          i32.const 1
          i32.store offset=76
          local.get $l3
          i32.const 1048968
          i32.store offset=72
          local.get $l3
          i64.const 4
          i64.store offset=80 align=4
          local.get $l3
          i32.const 72
          i32.add
          i32.const 1048976
          call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
          unreachable
        end
        local.get $l3
        i32.const 0
        i32.store offset=88
        local.get $l3
        i32.const 1
        i32.store offset=76
        local.get $l3
        i32.const 1049040
        i32.store offset=72
        local.get $l3
        i64.const 4
        i64.store offset=80 align=4
        local.get $l3
        i32.const 72
        i32.add
        i32.const 1049048
        call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
        unreachable
      end
      local.get $l3
      i32.const 0
      i32.store offset=88
      local.get $l3
      i32.const 1
      i32.store offset=76
      local.get $l3
      i32.const 1049116
      i32.store offset=72
      local.get $l3
      i64.const 4
      i64.store offset=80 align=4
      local.get $l3
      i32.const 72
      i32.add
      i32.const 1049124
      call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
      unreachable
    end
    i32.const 1049064
    call $_ZN4core9panicking11panic_const24panic_const_sub_overflow17hddb96f4b6b3b1af0E
    unreachable)
  (func $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h60a56e891f88b6daE (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p2
          i64.load
          local.tee $l4
          i32.wrap_i64
          i32.const 255
          i32.and
          local.tee $p2
          i32.const 69
          i32.eq
          br_if 0 (;@3;)
          local.get $p2
          i32.const 11
          i32.ne
          br_if 1 (;@2;)
          local.get $l3
          local.get $l4
          call $_ZN18soroban_env_common3num96_$LT$impl$u20$core..convert..From$LT$soroban_env_common..num..I128Small$GT$$u20$for$u20$i128$GT$4from17h71a6da86b2db2765E
          local.get $l3
          i64.load
          local.set $l4
          local.get $p0
          i32.const 16
          i32.add
          local.get $l3
          i32.const 8
          i32.add
          i64.load
          i64.store
          local.get $p0
          local.get $l4
          i64.store offset=8
          i64.const 0
          local.set $l4
          br 2 (;@1;)
        end
        local.get $p1
        local.get $l4
        call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$16obj_to_i128_hi6417h1b9fc5e530787d52E
        local.set $l5
        local.get $p1
        local.get $l4
        call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$16obj_to_i128_lo6417h45fe7b2355f2ac65E
        local.set $l4
        local.get $p0
        i32.const 16
        i32.add
        local.get $l5
        i64.store
        local.get $p0
        local.get $l4
        i64.store offset=8
        i64.const 0
        local.set $l4
        br 1 (;@1;)
      end
      local.get $p0
      call $_ZN120_$LT$soroban_env_common..error..Error$u20$as$u20$core..convert..From$LT$soroban_env_common..val..ConversionError$GT$$GT$4from17h830fb10c420e09b3E
      i64.store offset=8
      i64.const 1
      local.set $l4
    end
    local.get $p0
    local.get $l4
    i64.store
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h2c8d473123972f3dE (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $p1
    local.get $p2
    call $_ZN108_$LT$soroban_env_common..num..I128Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17hd2556d1f145ee649E
    local.get $p0
    local.get $l3
    i64.load offset=8
    i64.store offset=8
    local.get $p0
    i64.const 0
    i64.store
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN108_$LT$soroban_env_common..num..I128Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17hd2556d1f145ee649E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $p2
    i64.load
    local.tee $l4
    local.get $p2
    i32.const 8
    i32.add
    i64.load
    local.tee $l5
    call $_ZN89_$LT$soroban_env_common..num..I128Small$u20$as$u20$core..convert..TryFrom$LT$i128$GT$$GT$8try_from17h1a2854bb9b6b01ebE
    block  ;; label = @1
      block  ;; label = @2
        local.get $l3
        i64.load
        i32.wrap_i64
        br_if 0 (;@2;)
        local.get $l3
        i64.load offset=8
        local.set $l4
        br 1 (;@1;)
      end
      local.get $p1
      local.get $l5
      local.get $l4
      call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$20obj_from_i128_pieces17h39cc8a8582c438d0E
      local.set $l4
    end
    local.get $p0
    local.get $l4
    i64.store offset=8
    local.get $p0
    i64.const 0
    i64.store
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN106_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..num..U64Val$GT$$GT$12try_from_val17h58e660f8d835f477E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    i32.const 16
    i32.add
    local.get $p2
    i64.load
    local.tee $l4
    call $_ZN115_$LT$soroban_env_common..num..U64Small$u20$as$u20$core..convert..TryFrom$LT$soroban_env_common..num..U64Val$GT$$GT$8try_from17h4be77cef942d4136E
    block  ;; label = @1
      block  ;; label = @2
        local.get $l3
        i64.load offset=16
        i32.wrap_i64
        br_if 0 (;@2;)
        i64.const 0
        local.set $l4
        local.get $l3
        i64.load offset=24
        call $_ZN101_$LT$soroban_env_common..symbol..SymbolSmall$u20$as$u20$core..iter..traits..collect..IntoIterator$GT$9into_iter17h96cb636c76edde29E
        local.set $l5
        br 1 (;@1;)
      end
      local.get $l3
      local.get $l4
      call $_ZN116_$LT$soroban_env_common..num..U64Object$u20$as$u20$core..convert..TryFrom$LT$soroban_env_common..num..U64Val$GT$$GT$8try_from17hd08847d12ef34fbbE
      block  ;; label = @2
        local.get $l3
        i64.load
        i32.wrap_i64
        br_if 0 (;@2;)
        i64.const 0
        local.set $l4
        local.get $p1
        local.get $l3
        i64.load offset=8
        call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$10obj_to_u6417h7254f25bd022b510E
        local.set $l5
        br 1 (;@1;)
      end
      i64.const 1
      local.set $l4
      call $_ZN120_$LT$soroban_env_common..error..Error$u20$as$u20$core..convert..From$LT$soroban_env_common..val..ConversionError$GT$$GT$4from17h830fb10c420e09b3E
      local.set $l5
    end
    local.get $p0
    local.get $l5
    i64.store offset=8
    local.get $p0
    local.get $l4
    i64.store
    local.get $l3
    i32.const 32
    i32.add
    global.set $__stack_pointer)
  (func $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17hbb31fccf356a3e45E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $p2
    i64.load align=4
    i64.store offset=24 align=4
    local.get $l3
    i32.const 8
    i32.add
    local.get $p1
    local.get $l3
    i32.const 24
    i32.add
    call $_ZN122_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$$u5b$u8$u5d$$GT$$GT$12try_from_val17h812c502b86f0738aE
    local.get $l3
    i64.load offset=8
    local.set $l4
    local.get $p0
    local.get $l3
    i64.load offset=16
    i64.store offset=8
    local.get $p0
    local.get $l4
    i64.store
    local.get $l3
    i32.const 32
    i32.add
    global.set $__stack_pointer)
  (func $_ZN122_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$$u5b$u8$u5d$$GT$$GT$12try_from_val17h812c502b86f0738aE (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i32) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $p2
    i32.load
    local.tee $l4
    local.get $p2
    i32.load offset=4
    local.tee $p2
    call $_ZN18soroban_env_common6symbol11SymbolSmall14try_from_bytes17hed93845967fa2df2E
    block  ;; label = @1
      block  ;; label = @2
        local.get $l3
        i32.load
        br_if 0 (;@2;)
        local.get $l3
        i64.load offset=8
        local.set $l5
        br 1 (;@1;)
      end
      local.get $p1
      local.get $l4
      local.get $p2
      call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$21symbol_new_from_slice17h9223d9902a1a6d47E
      local.set $l5
    end
    local.get $p0
    local.get $l5
    i64.store offset=8
    local.get $p0
    i64.const 0
    i64.store
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h0b335473af49db75E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    local.get $p0
    local.get $p1
    i64.load
    i64.store offset=8
    local.get $p0
    i64.const 0
    i64.store)
  (func $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h941971ca3e19786fE (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $p1
    local.get $p2
    call $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17hbb31fccf356a3e45E
    local.get $p0
    local.get $l3
    i64.load offset=8
    i64.store offset=8
    local.get $p0
    i64.const 0
    i64.store
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h20bfac56f373f0fbE (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i64)
    local.get $p0
    local.get $p1
    i64.load
    local.tee $l3
    i64.store offset=8
    local.get $p0
    local.get $l3
    i64.const 255
    i64.and
    i64.const 75
    i64.ne
    i64.extend_i32_u
    i64.store)
  (func $_ZN11soroban_sdk3vec19VecTryIter$LT$T$GT$3new17hf032d0bf5104dcdbE (type $t13) (param $p0 i32) (param $p1 i64)
    (local $l2 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    local.get $p1
    i64.store offset=8
    local.get $p0
    local.get $l2
    i32.const 16
    i32.add
    local.get $p1
    call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$7vec_len17h7609c60b3ed511f1E
    call $_ZN18soroban_env_common3num92_$LT$impl$u20$core..convert..From$LT$soroban_env_common..num..I32Val$GT$$u20$for$u20$i32$GT$4from17hfd042b091018bf24E
    i32.store offset=12
    local.get $p0
    i32.const 0
    i32.store offset=8
    local.get $p0
    local.get $l2
    i64.load offset=8
    i64.store
    local.get $l2
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hb9b532c12128b442E (type $t14) (param $p0 i32) (param $p1 i32)
    (local $l2 i32) (local $l3 i64) (local $l4 i64)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p1
        i32.load offset=8
        local.tee $l2
        local.get $p1
        i32.load offset=12
        i32.lt_u
        br_if 0 (;@2;)
        i64.const 2
        local.set $l3
        br 1 (;@1;)
      end
      local.get $p1
      i32.const 8
      i32.add
      local.get $p1
      i64.load
      local.get $l2
      call $_ZN82_$LT$soroban_env_common..num..U32Val$u20$as$u20$core..convert..From$LT$u32$GT$$GT$4from17h853f8bad0f87a0b0E
      call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$7vec_get17hdf8d6f9b6c1491adE
      local.set $l4
      local.get $p1
      local.get $l2
      i32.const 1
      i32.add
      i32.store offset=8
      i64.const 0
      local.set $l3
    end
    local.get $p0
    local.get $l4
    i64.store offset=8
    local.get $p0
    local.get $l3
    i64.store)
  (func $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17ha9ab042519fc6232E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i64)
    local.get $p2
    i64.load
    local.tee $l3
    call $_ZN90_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..val..ValConvert$GT$11is_val_type17h8d256ae0615aad90E
    local.set $p2
    local.get $p0
    local.get $l3
    i64.store offset=8
    local.get $p0
    local.get $p2
    i32.const 1
    i32.xor
    i64.extend_i32_u
    i64.store)
  (func $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h52b4cfee374261f2E (type $t15) (param $p0 i32) (result i32)
    (local $l1 i32)
    block  ;; label = @1
      local.get $p0
      i32.load offset=12
      local.tee $l1
      local.get $p0
      i32.load offset=8
      local.tee $p0
      i32.lt_u
      br_if 0 (;@1;)
      local.get $l1
      local.get $p0
      i32.sub
      return
    end
    i32.const 1049580
    call $_ZN4core9panicking11panic_const24panic_const_sub_overflow17hddb96f4b6b3b1af0E
    unreachable)
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h5ae9c792ed9ddb0aE (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i64)
    local.get $p0
    local.get $p1
    i64.load
    local.tee $l3
    i64.store offset=8
    local.get $p0
    local.get $l3
    i64.const 255
    i64.and
    i64.const 77
    i64.ne
    i64.extend_i32_u
    i64.store)
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hcddf0191ee673ce5E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    local.get $p0
    local.get $p1
    i64.load
    i64.store offset=8
    local.get $p0
    i64.const 0
    i64.store)
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hff8c2adbd7f91526E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $l3
    local.get $p1
    call $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17ha9ab042519fc6232E
    local.get $l3
    i64.load
    local.set $l4
    local.get $p0
    local.get $l3
    i64.load offset=8
    i64.store offset=8
    local.get $p0
    local.get $l4
    i64.store
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN77_$LT$soroban_env_common..val..ConversionError$u20$as$u20$core..fmt..Debug$GT$3fmt17h436be35266574685E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p1
    i32.const 1049216
    i32.const 15
    call $_ZN4core3fmt9Formatter9write_str17h89c4071b72e49099E)
  (func $rust_begin_unwind (type $t16) (param $p0 i32)
    unreachable
    unreachable)
  (func $_ (type $t17))
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hc8b691dc1c6bcc69E (type $t8) (param $p0 i32) (param $p1 i32) (result i64)
    local.get $p0
    i64.load)
  (func $_ZN11soroban_sdk3env3Env24current_contract_address17h8e55331aeccd768aE (type $t18) (param $p0 i32) (result i64)
    local.get $p0
    call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$28get_current_contract_address17h8e0670847fc49c85E)
  (func $_ZN11soroban_sdk3env3Env15invoke_contract17h8088c2d4a386672fE (type $t9) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i64)
    (local $l4 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l4
    global.set $__stack_pointer
    block  ;; label = @1
      local.get $p0
      local.get $p1
      i64.load
      local.get $p2
      i64.load
      local.get $p3
      call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$4call17h39c544f19ed1c69eE
      i64.const 255
      i64.and
      i64.const 2
      i64.eq
      br_if 0 (;@1;)
      i32.const 1049156
      i32.const 43
      local.get $l4
      i32.const 15
      i32.add
      i32.const 1049140
      i32.const 1049336
      call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
      unreachable
    end
    local.get $l4
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h46c1f0b4bb90c3afE (type $t19) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (param $p4 i32) (result i64)
    local.get $p0
    local.get $p1
    local.get $p2
    local.get $p3
    local.get $p4
    call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17hfc470755612a9367E)
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17he2c6fd8b8e43f65aE (type $t20) (param $p0 i32) (param $p1 i64) (param $p2 i32) (param $p3 i32) (param $p4 i32) (param $p5 i32) (result i64)
    local.get $p0
    local.get $p1
    local.get $p2
    local.get $p3
    local.get $p4
    local.get $p5
    call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h83ccf6544c10dac0E)
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hc5c8d35ed2002e9bE (type $t21) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i64)
    local.get $p0
    local.get $p1
    local.get $p2
    call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17ha04003c8c7ab44b9E)
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$20symbol_index_in_strs17hb337be2c8bdc7236E (type $t22) (param $p0 i32) (param $p1 i64) (param $p2 i32) (param $p3 i32) (result i64)
    local.get $p0
    local.get $p1
    local.get $p2
    local.get $p3
    call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$20symbol_index_in_strs17h4e4b82b88b2047a5E)
  (func $_ZN149_$LT$soroban_sdk..address..Address$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h8d74483e028fd698E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i64)
    local.get $p0
    local.get $p2
    i64.load
    local.tee $l3
    i64.store offset=8
    local.get $p0
    local.get $l3
    i64.const 255
    i64.and
    i64.const 77
    i64.ne
    i64.extend_i32_u
    i64.store)
  (func $_ZN11soroban_sdk7address7Address12require_auth17h2b3188645da2623eE (type $t16) (param $p0 i32)
    local.get $p0
    i32.const 8
    i32.add
    local.get $p0
    i64.load
    call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$12require_auth17h145a7269260671d5E
    drop)
  (func $_ZN11soroban_sdk6ledger6Ledger9timestamp17h482cdd452385aa10E (type $t18) (param $p0 i32) (result i64)
    (local $l1 i32) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    local.get $p0
    call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$20get_ledger_timestamp17h0f1b2791cdd5b463E
    i64.store offset=16
    local.get $l1
    local.get $p0
    local.get $l1
    i32.const 16
    i32.add
    call $_ZN106_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..num..U64Val$GT$$GT$12try_from_val17h58e660f8d835f477E
    local.get $l1
    i64.load offset=8
    local.set $l2
    block  ;; label = @1
      local.get $l1
      i32.load
      i32.eqz
      br_if 0 (;@1;)
      local.get $l1
      local.get $l2
      i64.store offset=24
      i32.const 1049156
      i32.const 43
      local.get $l1
      i32.const 24
      i32.add
      i32.const 1049200
      i32.const 1049460
      call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
      unreachable
    end
    local.get $l1
    i32.const 32
    i32.add
    global.set $__stack_pointer
    local.get $l2)
  (func $_ZN11soroban_sdk4prng4Prng3new17h80882443cd5683a7E (type $t16) (param $p0 i32))
  (func $_ZN11soroban_sdk7storage7Storage12has_internal17h76da7d30a596b93aE (type $t23) (param $p0 i32) (param $p1 i64) (param $p2 i64) (result i32)
    local.get $p0
    local.get $p1
    local.get $p2
    call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$17has_contract_data17hc9870eb00e614177E
    call $_ZN18soroban_env_common3val91_$LT$impl$u20$core..convert..From$LT$soroban_env_common..val..Bool$GT$$u20$for$u20$bool$GT$4from17h839bcb8113c84479E)
  (func $_ZN11soroban_sdk7storage7Storage12get_internal17h0c3bb0d738b8e739E (type $t24) (param $p0 i32) (param $p1 i64) (param $p2 i64) (result i64)
    local.get $p0
    local.get $p1
    local.get $p2
    call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$17get_contract_data17h57b556d5f81bc092E)
  (func $_ZN69_$LT$soroban_sdk..vec..Vec$LT$T$GT$$u20$as$u20$core..clone..Clone$GT$5clone17h7ebc08ea59ba3b99E (type $t18) (param $p0 i32) (result i64)
    local.get $p0
    i64.load)
  (func $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$12obj_from_u6417hfec479798a3b31dcE (type $t25) (param $p0 i32) (param $p1 i64) (result i64)
    local.get $p0
    local.get $p1
    call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$12obj_from_u6417h88a8c57b2d77ffd1E)
  (func $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$10obj_to_u6417hb85eb8f9dd45bf0aE (type $t25) (param $p0 i32) (param $p1 i64) (result i64)
    local.get $p0
    local.get $p1
    call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$10obj_to_u6417h7254f25bd022b510E)
  (func $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$7vec_len17h31d93a0baf23dfbbE (type $t25) (param $p0 i32) (param $p1 i64) (result i64)
    local.get $p0
    local.get $p1
    call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$7vec_len17h7609c60b3ed511f1E)
  (func $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$18vec_first_index_of17h92d165a34b0e6360E (type $t24) (param $p0 i32) (param $p1 i64) (param $p2 i64) (result i64)
    local.get $p0
    local.get $p1
    local.get $p2
    call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$18vec_first_index_of17hc56bd73924fa1498E)
  (func $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$17put_contract_data17hdee22151560b1714E (type $t26) (param $p0 i32) (param $p1 i64) (param $p2 i64) (param $p3 i64) (result i64)
    local.get $p0
    local.get $p1
    local.get $p2
    local.get $p3
    call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$17put_contract_data17h7552595f7d1691a5E)
  (func $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$17del_contract_data17h9b108e7191bde848E (type $t24) (param $p0 i32) (param $p1 i64) (param $p2 i64) (result i64)
    local.get $p0
    local.get $p1
    local.get $p2
    call $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$17del_contract_data17h474ed8f18eda962cE)
  (func $_ZN11soroban_sdk5token11TokenClient3new17h87e13961d8149299E (type $t8) (param $p0 i32) (param $p1 i32) (result i64)
    local.get $p1
    i64.load)
  (func $_ZN11soroban_sdk5token11TokenClient8transfer17h3a967ba5161c1b0dE (type $t27) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32)
    (local $l4 i32) (local $l5 i64) (local $l6 i64)
    global.get $__stack_pointer
    i32.const 64
    i32.sub
    local.tee $l4
    global.set $__stack_pointer
    local.get $p1
    i64.load
    local.set $l5
    local.get $p2
    i64.load
    local.set $l6
    local.get $l4
    local.get $p0
    i32.const 8
    i32.add
    local.tee $p2
    local.get $p3
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h2c8d473123972f3dE
    local.get $l4
    local.get $l6
    i64.store offset=24
    local.get $l4
    local.get $l5
    i64.store offset=16
    local.get $l4
    local.get $l4
    i64.load offset=8
    i64.store offset=32
    i32.const 0
    local.set $p1
    loop  ;; label = @1
      block  ;; label = @2
        local.get $p1
        i32.const 24
        i32.ne
        br_if 0 (;@2;)
        i32.const 0
        local.set $p1
        block  ;; label = @3
          loop  ;; label = @4
            local.get $p1
            i32.const 24
            i32.eq
            br_if 1 (;@3;)
            local.get $l4
            i32.const 40
            i32.add
            local.get $p1
            i32.add
            local.get $l4
            i32.const 16
            i32.add
            local.get $p1
            i32.add
            i64.load
            i64.store
            local.get $p1
            i32.const 8
            i32.add
            local.set $p1
            br 0 (;@4;)
          end
        end
        local.get $p2
        local.get $p0
        i32.const 1049600
        local.get $p2
        local.get $l4
        i32.const 40
        i32.add
        i32.const 3
        call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17ha04003c8c7ab44b9E
        call $_ZN11soroban_sdk3env3Env15invoke_contract17h8088c2d4a386672fE
        local.get $l4
        i32.const 64
        i32.add
        global.set $__stack_pointer
        return
      end
      local.get $l4
      i32.const 40
      i32.add
      local.get $p1
      i32.add
      i64.const 2
      i64.store
      local.get $p1
      i32.const 8
      i32.add
      local.set $p1
      br 0 (;@1;)
    end)
  (func $_ZN11soroban_sdk3num4I2566to_val17ha5879f16a4e765c3E (type $t18) (param $p0 i32) (result i64)
    local.get $p0
    i64.load)
  (func $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$21symbol_new_from_slice17h9223d9902a1a6d47E (type $t21) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i64)
    local.get $p1
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    local.get $p2
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    call $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17hb02212a3b885b74aE)
  (func $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17hfc470755612a9367E (type $t19) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (param $p4 i32) (result i64)
    block  ;; label = @1
      local.get $p2
      local.get $p4
      i32.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p1
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    local.get $p3
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    local.get $p2
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    call $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17h1462d18b9e5fcf8fE)
  (func $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h83ccf6544c10dac0E (type $t20) (param $p0 i32) (param $p1 i64) (param $p2 i32) (param $p3 i32) (param $p4 i32) (param $p5 i32) (result i64)
    block  ;; label = @1
      local.get $p3
      local.get $p5
      i32.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p1
    local.get $p2
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    local.get $p4
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    local.get $p3
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    call $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h19ad59f5b947b3cbE)
  (func $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17ha04003c8c7ab44b9E (type $t21) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i64)
    local.get $p1
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    local.get $p2
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    call $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17hfa3fd9016321cb70E)
  (func $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$20symbol_index_in_strs17h4e4b82b88b2047a5E (type $t22) (param $p0 i32) (param $p1 i64) (param $p2 i32) (param $p3 i32) (result i64)
    local.get $p1
    local.get $p2
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    local.get $p3
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    call $_ZN17soroban_env_guest5guest3buf29symbol_index_in_linear_memory17hdc10fd4d66dd77abE)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$20get_ledger_timestamp17h0f1b2791cdd5b463E (type $t18) (param $p0 i32) (result i64)
    call $_ZN17soroban_env_guest5guest7context20get_ledger_timestamp17h3dc89e3bc346e730E)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$28get_current_contract_address17h8e0670847fc49c85E (type $t18) (param $p0 i32) (result i64)
    call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17hd1d4b7bd620a8a13E)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$12obj_from_u6417h88a8c57b2d77ffd1E (type $t25) (param $p0 i32) (param $p1 i64) (result i64)
    local.get $p1
    call $_ZN17soroban_env_guest5guest3int12obj_from_u6417hf31ac87e20c7a2a1E)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$10obj_to_u6417h7254f25bd022b510E (type $t25) (param $p0 i32) (param $p1 i64) (result i64)
    local.get $p1
    call $_ZN17soroban_env_guest5guest3int10obj_to_u6417h6dd63be303104bf7E)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$20obj_from_i128_pieces17h39cc8a8582c438d0E (type $t24) (param $p0 i32) (param $p1 i64) (param $p2 i64) (result i64)
    local.get $p1
    local.get $p2
    call $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17hae61d1b41bca5c92E)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$16obj_to_i128_lo6417h45fe7b2355f2ac65E (type $t25) (param $p0 i32) (param $p1 i64) (result i64)
    local.get $p1
    call $_ZN17soroban_env_guest5guest3int16obj_to_i128_lo6417h473c1689f5477a10E)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$16obj_to_i128_hi6417h1b9fc5e530787d52E (type $t25) (param $p0 i32) (param $p1 i64) (result i64)
    local.get $p1
    call $_ZN17soroban_env_guest5guest3int16obj_to_i128_hi6417h4ad1bb58684df7baE)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$7vec_get17hdf8d6f9b6c1491adE (type $t24) (param $p0 i32) (param $p1 i64) (param $p2 i64) (result i64)
    local.get $p1
    local.get $p2
    call $_ZN17soroban_env_guest5guest3vec7vec_get17hed53bd0a40d2a5edE)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$7vec_len17h7609c60b3ed511f1E (type $t25) (param $p0 i32) (param $p1 i64) (result i64)
    local.get $p1
    call $_ZN17soroban_env_guest5guest3vec7vec_len17h8a9fdafaf3b67c35E)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$18vec_first_index_of17hc56bd73924fa1498E (type $t24) (param $p0 i32) (param $p1 i64) (param $p2 i64) (result i64)
    local.get $p1
    local.get $p2
    call $_ZN17soroban_env_guest5guest3vec18vec_first_index_of17h949a075abe17b538E)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$17put_contract_data17h7552595f7d1691a5E (type $t26) (param $p0 i32) (param $p1 i64) (param $p2 i64) (param $p3 i64) (result i64)
    local.get $p1
    local.get $p2
    local.get $p3
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h8ee4847deecad99bE)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$17has_contract_data17hc9870eb00e614177E (type $t24) (param $p0 i32) (param $p1 i64) (param $p2 i64) (result i64)
    local.get $p1
    local.get $p2
    call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17h8a7244d88b2a25e5E)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$17get_contract_data17h57b556d5f81bc092E (type $t24) (param $p0 i32) (param $p1 i64) (param $p2 i64) (result i64)
    local.get $p1
    local.get $p2
    call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17hb1d6d2751ce51aa8E)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$17del_contract_data17h474ed8f18eda962cE (type $t24) (param $p0 i32) (param $p1 i64) (param $p2 i64) (result i64)
    local.get $p1
    local.get $p2
    call $_ZN17soroban_env_guest5guest6ledger17del_contract_data17hf8d1baf5f895892dE)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$4call17h39c544f19ed1c69eE (type $t26) (param $p0 i32) (param $p1 i64) (param $p2 i64) (param $p3 i64) (result i64)
    local.get $p1
    local.get $p2
    local.get $p3
    call $_ZN17soroban_env_guest5guest4call4call17hbbe7ab5a2ad81809E)
  (func $_ZN80_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..Env$GT$12require_auth17h145a7269260671d5E (type $t25) (param $p0 i32) (param $p1 i64) (result i64)
    local.get $p1
    call $_ZN17soroban_env_guest5guest7address12require_auth17h3cca0ad538f0fd30E)
  (func $_ZN11stellar_xdr4curr9generated11ScErrorCode4name17h090eb02a9cca2592E (type $t14) (param $p0 i32) (param $p1 i32)
    local.get $p0
    local.get $p1
    i32.load
    i32.const 2
    i32.shl
    local.tee $p1
    i32.const 1049912
    i32.add
    i32.load
    i32.store offset=4
    local.get $p0
    local.get $p1
    i32.const 1049952
    i32.add
    i32.load
    i32.store)
  (func $_ZN11stellar_xdr4curr9generated11ScErrorType4name17hf7ef83d19007e301E (type $t14) (param $p0 i32) (param $p1 i32)
    local.get $p0
    local.get $p1
    i32.load
    i32.const 2
    i32.shl
    local.tee $p1
    i32.const 1049992
    i32.add
    i32.load
    i32.store offset=4
    local.get $p0
    local.get $p1
    i32.const 1050032
    i32.add
    i32.load
    i32.store)
  (func $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17h9c75e7f5eb72e75dE (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p0
    i32.load
    local.get $p0
    i32.load offset=4
    local.get $p1
    call $_ZN42_$LT$str$u20$as$u20$core..fmt..Display$GT$3fmt17ha62171cbd2687de4E)
  (func $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p0
    i32.load offset=20
    local.get $p0
    i32.load offset=24
    local.get $p1
    call $_ZN4core3fmt5write17hbbcd4b328f92d3c5E)
  (func $_ZN69_$LT$soroban_env_common..error..Error$u20$as$u20$core..fmt..Debug$GT$3fmt17h6121ab0f52dd5078E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32) (local $l3 i64) (local $l4 i32) (local $l5 i32)
    global.get $__stack_pointer
    i32.const 112
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    local.get $p0
    i64.load
    local.tee $l3
    i32.wrap_i64
    local.tee $p0
    i32.const 8
    i32.shr_u
    local.tee $l4
    i32.store offset=40
    local.get $l2
    local.get $l3
    i64.const 32
    i64.shr_u
    i32.wrap_i64
    local.tee $l5
    i32.store offset=44
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            local.get $p0
            i32.const 2559
            i32.gt_u
            br_if 0 (;@4;)
            local.get $l2
            local.get $l4
            i32.store offset=48
            local.get $p0
            i32.const 256
            i32.lt_u
            br_if 1 (;@3;)
            block  ;; label = @5
              local.get $l5
              i32.const 10
              i32.ge_u
              br_if 0 (;@5;)
              local.get $l2
              local.get $l5
              i32.store offset=52
              local.get $l2
              i32.const 16
              i32.add
              local.get $l2
              i32.const 48
              i32.add
              call $_ZN11stellar_xdr4curr9generated11ScErrorType4name17hf7ef83d19007e301E
              local.get $l2
              local.get $l2
              i64.load offset=16
              i64.store offset=56 align=4
              local.get $l2
              i32.const 8
              i32.add
              local.get $l2
              i32.const 52
              i32.add
              call $_ZN11stellar_xdr4curr9generated11ScErrorCode4name17h090eb02a9cca2592E
              local.get $l2
              i32.const 108
              i32.add
              i32.const 3
              i32.store
              local.get $l2
              i32.const 3
              i32.store offset=100
              local.get $l2
              i32.const 3
              i32.store offset=76
              local.get $l2
              i32.const 1049804
              i32.store offset=72
              local.get $l2
              i64.const 2
              i64.store offset=84 align=4
              local.get $l2
              local.get $l2
              i64.load offset=8
              i64.store offset=64 align=4
              local.get $l2
              local.get $l2
              i32.const 64
              i32.add
              i32.store offset=104
              local.get $l2
              local.get $l2
              i32.const 56
              i32.add
              i32.store offset=96
              local.get $l2
              local.get $l2
              i32.const 96
              i32.add
              i32.store offset=80
              local.get $p1
              local.get $l2
              i32.const 72
              i32.add
              call $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE
              local.set $p0
              br 4 (;@1;)
            end
            local.get $l2
            i32.const 24
            i32.add
            local.get $l2
            i32.const 48
            i32.add
            call $_ZN11stellar_xdr4curr9generated11ScErrorType4name17hf7ef83d19007e301E
            local.get $l2
            i32.const 108
            i32.add
            i32.const 4
            i32.store
            local.get $l2
            i32.const 3
            i32.store offset=100
            local.get $l2
            i32.const 3
            i32.store offset=76
            local.get $l2
            i32.const 1049832
            i32.store offset=72
            local.get $l2
            i64.const 2
            i64.store offset=84 align=4
            local.get $l2
            local.get $l2
            i64.load offset=24
            i64.store offset=64 align=4
            local.get $l2
            local.get $l2
            i32.const 44
            i32.add
            i32.store offset=104
            local.get $l2
            local.get $l2
            i32.const 64
            i32.add
            i32.store offset=96
            local.get $l2
            local.get $l2
            i32.const 96
            i32.add
            i32.store offset=80
            local.get $p1
            local.get $l2
            i32.const 72
            i32.add
            call $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE
            local.set $p0
            br 3 (;@1;)
          end
          local.get $l5
          i32.const 10
          i32.lt_u
          br_if 1 (;@2;)
          local.get $l2
          i32.const 108
          i32.add
          i32.const 4
          i32.store
          local.get $l2
          i32.const 3
          i32.store offset=76
          local.get $l2
          i32.const 1049888
          i32.store offset=72
          local.get $l2
          i64.const 2
          i64.store offset=84 align=4
          local.get $l2
          i32.const 4
          i32.store offset=100
          local.get $l2
          local.get $l2
          i32.const 96
          i32.add
          i32.store offset=80
          local.get $l2
          local.get $l2
          i32.const 44
          i32.add
          i32.store offset=104
          local.get $l2
          local.get $l2
          i32.const 40
          i32.add
          i32.store offset=96
          local.get $p1
          local.get $l2
          i32.const 72
          i32.add
          call $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE
          local.set $p0
          br 2 (;@1;)
        end
        local.get $l2
        local.get $l2
        i32.const 48
        i32.add
        call $_ZN11stellar_xdr4curr9generated11ScErrorType4name17hf7ef83d19007e301E
        local.get $l2
        i32.const 108
        i32.add
        i32.const 4
        i32.store
        local.get $l2
        i32.const 3
        i32.store offset=100
        local.get $l2
        i32.const 3
        i32.store offset=76
        local.get $l2
        i32.const 1049832
        i32.store offset=72
        local.get $l2
        i64.const 2
        i64.store offset=84 align=4
        local.get $l2
        local.get $l2
        i64.load
        i64.store offset=64 align=4
        local.get $l2
        local.get $l2
        i32.const 44
        i32.add
        i32.store offset=104
        local.get $l2
        local.get $l2
        i32.const 64
        i32.add
        i32.store offset=96
        local.get $l2
        local.get $l2
        i32.const 96
        i32.add
        i32.store offset=80
        local.get $p1
        local.get $l2
        i32.const 72
        i32.add
        call $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE
        local.set $p0
        br 1 (;@1;)
      end
      local.get $l2
      local.get $l5
      i32.store offset=56
      local.get $l2
      i32.const 32
      i32.add
      local.get $l2
      i32.const 56
      i32.add
      call $_ZN11stellar_xdr4curr9generated11ScErrorCode4name17h090eb02a9cca2592E
      local.get $l2
      i32.const 108
      i32.add
      i32.const 3
      i32.store
      local.get $l2
      i32.const 4
      i32.store offset=100
      local.get $l2
      i32.const 3
      i32.store offset=76
      local.get $l2
      i32.const 1049864
      i32.store offset=72
      local.get $l2
      i64.const 2
      i64.store offset=84 align=4
      local.get $l2
      local.get $l2
      i64.load offset=32
      i64.store offset=64 align=4
      local.get $l2
      local.get $l2
      i32.const 64
      i32.add
      i32.store offset=104
      local.get $l2
      local.get $l2
      i32.const 40
      i32.add
      i32.store offset=96
      local.get $l2
      local.get $l2
      i32.const 96
      i32.add
      i32.store offset=80
      local.get $p1
      local.get $l2
      i32.const 72
      i32.add
      call $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE
      local.set $p0
    end
    local.get $l2
    i32.const 112
    i32.add
    global.set $__stack_pointer
    local.get $p0)
  (func $_ZN120_$LT$soroban_env_common..error..Error$u20$as$u20$core..convert..From$LT$soroban_env_common..val..ConversionError$GT$$GT$4from17h830fb10c420e09b3E (type $t5) (result i64)
    i64.const 34359740419)
  (func $_ZN18soroban_env_common6symbol11SymbolSmall14try_from_bytes17hed93845967fa2df2E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        local.get $p2
        i32.const 9
        i32.gt_u
        br_if 0 (;@2;)
        i64.const 0
        local.set $l4
        loop  ;; label = @3
          block  ;; label = @4
            local.get $p2
            br_if 0 (;@4;)
            local.get $p0
            i32.const 0
            i32.store
            local.get $p0
            local.get $l4
            i64.const 8
            i64.shl
            i64.const 14
            i64.or
            i64.store offset=8
            br 3 (;@1;)
          end
          local.get $l3
          i32.const 8
          i32.add
          local.get $p1
          i32.load8_u
          call $_ZN18soroban_env_common6symbol11SymbolSmall11encode_byte17h72492252126254f4E
          block  ;; label = @4
            local.get $l3
            i32.load8_u offset=8
            i32.const 3
            i32.eq
            br_if 0 (;@4;)
            local.get $p0
            local.get $l3
            i64.load offset=8
            i64.store offset=4 align=4
            local.get $p0
            i32.const 1
            i32.store
            br 3 (;@1;)
          end
          local.get $p1
          i32.const 1
          i32.add
          local.set $p1
          local.get $p2
          i32.const -1
          i32.add
          local.set $p2
          local.get $l4
          i64.const 6
          i64.shl
          local.get $l3
          i64.load8_u offset=9
          i64.or
          local.set $l4
          br 0 (;@3;)
        end
      end
      local.get $p0
      local.get $p2
      i32.store offset=8
      local.get $p0
      i32.const 0
      i32.store8 offset=4
      local.get $p0
      i32.const 1
      i32.store
    end
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN18soroban_env_common6symbol11SymbolSmall11encode_byte17h72492252126254f4E (type $t14) (param $p0 i32) (param $p1 i32)
    (local $l2 i32)
    i32.const 1
    local.set $l2
    block  ;; label = @1
      local.get $p1
      i32.const 255
      i32.and
      i32.const 95
      i32.eq
      br_if 0 (;@1;)
      block  ;; label = @2
        local.get $p1
        i32.const -48
        i32.add
        i32.const 255
        i32.and
        i32.const 10
        i32.lt_u
        br_if 0 (;@2;)
        block  ;; label = @3
          local.get $p1
          i32.const -65
          i32.add
          i32.const 255
          i32.and
          i32.const 26
          i32.lt_u
          br_if 0 (;@3;)
          block  ;; label = @4
            local.get $p1
            i32.const -97
            i32.add
            i32.const 255
            i32.and
            i32.const 26
            i32.lt_u
            br_if 0 (;@4;)
            local.get $p0
            local.get $p1
            i32.store8 offset=1
            local.get $p0
            i32.const 1
            i32.store8
            return
          end
          local.get $p1
          i32.const -59
          i32.add
          local.set $l2
          br 2 (;@1;)
        end
        local.get $p1
        i32.const -53
        i32.add
        local.set $l2
        br 1 (;@1;)
      end
      local.get $p1
      i32.const -46
      i32.add
      local.set $l2
    end
    local.get $p0
    i32.const 3
    i32.store8
    local.get $p0
    local.get $l2
    i32.store8 offset=1)
  (func $_ZN101_$LT$soroban_env_common..symbol..SymbolSmall$u20$as$u20$core..iter..traits..collect..IntoIterator$GT$9into_iter17h96cb636c76edde29E (type $t6) (param $p0 i64) (result i64)
    local.get $p0
    i64.const 8
    i64.shr_u)
  (func $_ZN18soroban_env_common3val91_$LT$impl$u20$core..convert..From$LT$soroban_env_common..val..Bool$GT$$u20$for$u20$bool$GT$4from17h839bcb8113c84479E (type $t28) (param $p0 i64) (result i32)
    local.get $p0
    i64.const 1
    i64.eq)
  (func $_ZN82_$LT$soroban_env_common..num..U32Val$u20$as$u20$core..convert..From$LT$u32$GT$$GT$4from17h853f8bad0f87a0b0E (type $t18) (param $p0 i32) (result i64)
    local.get $p0
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or)
  (func $_ZN18soroban_env_common3num92_$LT$impl$u20$core..convert..From$LT$soroban_env_common..num..I32Val$GT$$u20$for$u20$i32$GT$4from17hfd042b091018bf24E (type $t28) (param $p0 i64) (result i32)
    local.get $p0
    i64.const 32
    i64.shr_u
    i32.wrap_i64)
  (func $_ZN18soroban_env_common3num96_$LT$impl$u20$core..convert..From$LT$soroban_env_common..num..I128Small$GT$$u20$for$u20$i128$GT$4from17h71a6da86b2db2765E (type $t13) (param $p0 i32) (param $p1 i64)
    local.get $p0
    local.get $p1
    i64.const 63
    i64.shr_s
    i64.store offset=8
    local.get $p0
    local.get $p1
    i64.const 8
    i64.shr_s
    i64.store)
  (func $_ZN87_$LT$soroban_env_common..num..U64Small$u20$as$u20$core..convert..TryFrom$LT$u64$GT$$GT$8try_from17h42d186eeb2ac18e2E (type $t13) (param $p0 i32) (param $p1 i64)
    local.get $p0
    local.get $p1
    i64.const 8
    i64.shl
    i64.const 6
    i64.or
    i64.store offset=8
    local.get $p0
    local.get $p1
    i64.const 72057594037927935
    i64.gt_u
    i64.extend_i32_u
    i64.store)
  (func $_ZN89_$LT$soroban_env_common..num..I128Small$u20$as$u20$core..convert..TryFrom$LT$i128$GT$$GT$8try_from17h1a2854bb9b6b01ebE (type $t29) (param $p0 i32) (param $p1 i64) (param $p2 i64)
    local.get $p0
    local.get $p1
    i64.const 8
    i64.shl
    i64.const 11
    i64.or
    i64.store offset=8
    local.get $p0
    local.get $p1
    i64.const -36028797018963968
    i64.add
    i64.const -72057594037927936
    i64.lt_u
    local.get $p1
    i64.const 63
    i64.shr_s
    local.get $p2
    i64.xor
    i64.const 0
    i64.ne
    i32.or
    i64.extend_i32_u
    i64.store)
  (func $_ZN90_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..val..ValConvert$GT$11is_val_type17h8d256ae0615aad90E (type $t28) (param $p0 i64) (result i32)
    (local $l1 i32)
    local.get $p0
    i32.wrap_i64
    i32.const 255
    i32.and
    local.tee $l1
    i32.const 14
    i32.eq
    local.get $l1
    i32.const 74
    i32.eq
    i32.or)
  (func $_ZN115_$LT$soroban_env_common..num..U64Small$u20$as$u20$core..convert..TryFrom$LT$soroban_env_common..num..U64Val$GT$$GT$8try_from17h4be77cef942d4136E (type $t13) (param $p0 i32) (param $p1 i64)
    local.get $p0
    local.get $p1
    i64.store offset=8
    local.get $p0
    local.get $p1
    i64.const 255
    i64.and
    i64.const 6
    i64.ne
    i64.extend_i32_u
    i64.store)
  (func $_ZN116_$LT$soroban_env_common..num..U64Object$u20$as$u20$core..convert..TryFrom$LT$soroban_env_common..num..U64Val$GT$$GT$8try_from17hd08847d12ef34fbbE (type $t13) (param $p0 i32) (param $p1 i64)
    local.get $p0
    local.get $p1
    i64.store offset=8
    local.get $p0
    local.get $p1
    i64.const 255
    i64.and
    i64.const 64
    i64.ne
    i64.extend_i32_u
    i64.store)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t14) (param $p0 i32) (param $p1 i32)
    (local $l2 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    i32.const 16
    i32.add
    local.get $p0
    i32.const 16
    i32.add
    i64.load align=4
    i64.store
    local.get $l2
    i32.const 8
    i32.add
    local.get $p0
    i32.const 8
    i32.add
    i64.load align=4
    i64.store
    local.get $l2
    i32.const 1
    i32.store16 offset=28
    local.get $l2
    local.get $p1
    i32.store offset=24
    local.get $l2
    local.get $p0
    i64.load align=4
    i64.store
    local.get $l2
    call $rust_begin_unwind
    unreachable)
  (func $_ZN4core3fmt9Formatter3pad17hdad3e25ba05328b0E (type $t0) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32) (local $l7 i32) (local $l8 i32)
    block  ;; label = @1
      local.get $p0
      i32.load
      local.tee $l3
      local.get $p0
      i32.load offset=8
      local.tee $l4
      i32.or
      i32.eqz
      br_if 0 (;@1;)
      block  ;; label = @2
        local.get $l4
        i32.eqz
        br_if 0 (;@2;)
        local.get $p1
        local.get $p2
        i32.add
        local.set $l5
        block  ;; label = @3
          block  ;; label = @4
            local.get $p0
            i32.load offset=12
            local.tee $l6
            br_if 0 (;@4;)
            i32.const 0
            local.set $l7
            local.get $p1
            local.set $l8
            br 1 (;@3;)
          end
          i32.const 0
          local.set $l7
          local.get $p1
          local.set $l8
          loop  ;; label = @4
            local.get $l8
            local.tee $l4
            local.get $l5
            i32.eq
            br_if 2 (;@2;)
            block  ;; label = @5
              block  ;; label = @6
                local.get $l4
                i32.load8_s
                local.tee $l8
                i32.const -1
                i32.le_s
                br_if 0 (;@6;)
                local.get $l4
                i32.const 1
                i32.add
                local.set $l8
                br 1 (;@5;)
              end
              block  ;; label = @6
                local.get $l8
                i32.const -32
                i32.ge_u
                br_if 0 (;@6;)
                local.get $l4
                i32.const 2
                i32.add
                local.set $l8
                br 1 (;@5;)
              end
              block  ;; label = @6
                local.get $l8
                i32.const -16
                i32.ge_u
                br_if 0 (;@6;)
                local.get $l4
                i32.const 3
                i32.add
                local.set $l8
                br 1 (;@5;)
              end
              local.get $l4
              i32.const 4
              i32.add
              local.set $l8
            end
            local.get $l8
            local.get $l4
            i32.sub
            local.get $l7
            i32.add
            local.set $l7
            local.get $l6
            i32.const -1
            i32.add
            local.tee $l6
            br_if 0 (;@4;)
          end
        end
        local.get $l8
        local.get $l5
        i32.eq
        br_if 0 (;@2;)
        block  ;; label = @3
          local.get $l8
          i32.load8_s
          local.tee $l4
          i32.const -1
          i32.gt_s
          br_if 0 (;@3;)
          local.get $l4
          i32.const -32
          i32.lt_u
          drop
        end
        block  ;; label = @3
          block  ;; label = @4
            local.get $l7
            i32.eqz
            br_if 0 (;@4;)
            block  ;; label = @5
              local.get $l7
              local.get $p2
              i32.ge_u
              br_if 0 (;@5;)
              i32.const 0
              local.set $l4
              local.get $p1
              local.get $l7
              i32.add
              i32.load8_s
              i32.const -65
              i32.gt_s
              br_if 1 (;@4;)
              br 2 (;@3;)
            end
            i32.const 0
            local.set $l4
            local.get $l7
            local.get $p2
            i32.ne
            br_if 1 (;@3;)
          end
          local.get $p1
          local.set $l4
        end
        local.get $l7
        local.get $p2
        local.get $l4
        select
        local.set $p2
        local.get $l4
        local.get $p1
        local.get $l4
        select
        local.set $p1
      end
      block  ;; label = @2
        local.get $l3
        br_if 0 (;@2;)
        local.get $p0
        i32.load offset=20
        local.get $p1
        local.get $p2
        local.get $p0
        i32.load offset=24
        i32.load offset=12
        call_indirect $T0 (type $t0)
        return
      end
      local.get $p0
      i32.load offset=4
      local.set $l3
      block  ;; label = @2
        block  ;; label = @3
          local.get $p2
          i32.const 16
          i32.lt_u
          br_if 0 (;@3;)
          local.get $p1
          local.get $p2
          call $_ZN4core3str5count14do_count_chars17h5612f5cea15e8f3fE
          local.set $l4
          br 1 (;@2;)
        end
        block  ;; label = @3
          local.get $p2
          br_if 0 (;@3;)
          i32.const 0
          local.set $l4
          br 1 (;@2;)
        end
        local.get $p2
        i32.const 3
        i32.and
        local.set $l6
        block  ;; label = @3
          block  ;; label = @4
            local.get $p2
            i32.const 4
            i32.ge_u
            br_if 0 (;@4;)
            i32.const 0
            local.set $l4
            i32.const 0
            local.set $l7
            br 1 (;@3;)
          end
          local.get $p2
          i32.const 12
          i32.and
          local.set $l5
          i32.const 0
          local.set $l4
          i32.const 0
          local.set $l7
          loop  ;; label = @4
            local.get $l4
            local.get $p1
            local.get $l7
            i32.add
            local.tee $l8
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.get $l8
            i32.const 1
            i32.add
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.get $l8
            i32.const 2
            i32.add
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.get $l8
            i32.const 3
            i32.add
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.set $l4
            local.get $l5
            local.get $l7
            i32.const 4
            i32.add
            local.tee $l7
            i32.ne
            br_if 0 (;@4;)
          end
        end
        local.get $l6
        i32.eqz
        br_if 0 (;@2;)
        local.get $p1
        local.get $l7
        i32.add
        local.set $l8
        loop  ;; label = @3
          local.get $l4
          local.get $l8
          i32.load8_s
          i32.const -65
          i32.gt_s
          i32.add
          local.set $l4
          local.get $l8
          i32.const 1
          i32.add
          local.set $l8
          local.get $l6
          i32.const -1
          i32.add
          local.tee $l6
          br_if 0 (;@3;)
        end
      end
      block  ;; label = @2
        block  ;; label = @3
          local.get $l3
          local.get $l4
          i32.le_u
          br_if 0 (;@3;)
          local.get $l3
          local.get $l4
          i32.sub
          local.set $l5
          i32.const 0
          local.set $l4
          block  ;; label = @4
            block  ;; label = @5
              block  ;; label = @6
                local.get $p0
                i32.load8_u offset=32
                br_table 2 (;@4;) 0 (;@6;) 1 (;@5;) 2 (;@4;) 2 (;@4;)
              end
              local.get $l5
              local.set $l4
              i32.const 0
              local.set $l5
              br 1 (;@4;)
            end
            local.get $l5
            i32.const 1
            i32.shr_u
            local.set $l4
            local.get $l5
            i32.const 1
            i32.add
            i32.const 1
            i32.shr_u
            local.set $l5
          end
          local.get $l4
          i32.const 1
          i32.add
          local.set $l4
          local.get $p0
          i32.load offset=16
          local.set $l6
          local.get $p0
          i32.load offset=24
          local.set $l8
          local.get $p0
          i32.load offset=20
          local.set $l7
          loop  ;; label = @4
            local.get $l4
            i32.const -1
            i32.add
            local.tee $l4
            i32.eqz
            br_if 2 (;@2;)
            local.get $l7
            local.get $l6
            local.get $l8
            i32.load offset=16
            call_indirect $T0 (type $t1)
            i32.eqz
            br_if 0 (;@4;)
          end
          i32.const 1
          return
        end
        local.get $p0
        i32.load offset=20
        local.get $p1
        local.get $p2
        local.get $p0
        i32.load offset=24
        i32.load offset=12
        call_indirect $T0 (type $t0)
        return
      end
      i32.const 1
      local.set $l4
      block  ;; label = @2
        local.get $l7
        local.get $p1
        local.get $p2
        local.get $l8
        i32.load offset=12
        call_indirect $T0 (type $t0)
        br_if 0 (;@2;)
        i32.const 0
        local.set $l4
        block  ;; label = @3
          loop  ;; label = @4
            block  ;; label = @5
              local.get $l5
              local.get $l4
              i32.ne
              br_if 0 (;@5;)
              local.get $l5
              local.set $l4
              br 2 (;@3;)
            end
            local.get $l4
            i32.const 1
            i32.add
            local.set $l4
            local.get $l7
            local.get $l6
            local.get $l8
            i32.load offset=16
            call_indirect $T0 (type $t1)
            i32.eqz
            br_if 0 (;@4;)
          end
          local.get $l4
          i32.const -1
          i32.add
          local.set $l4
        end
        local.get $l4
        local.get $l5
        i32.lt_u
        local.set $l4
      end
      local.get $l4
      return
    end
    local.get $p0
    i32.load offset=20
    local.get $p1
    local.get $p2
    local.get $p0
    i32.load offset=24
    i32.load offset=12
    call_indirect $T0 (type $t0))
  (func $_ZN4core9panicking5panic17hcaca2598a27ec0fcE (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    i32.const 0
    i32.store offset=16
    local.get $l3
    i32.const 1
    i32.store offset=4
    local.get $l3
    i64.const 4
    i64.store offset=8 align=4
    local.get $l3
    local.get $p1
    i32.store offset=28
    local.get $l3
    local.get $p0
    i32.store offset=24
    local.get $l3
    local.get $l3
    i32.const 24
    i32.add
    i32.store
    local.get $l3
    local.get $p2
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core3fmt5write17hbbcd4b328f92d3c5E (type $t0) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32) (local $l7 i32) (local $l8 i32) (local $l9 i32) (local $l10 i32) (local $l11 i32) (local $l12 i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    i32.const 3
    i32.store8 offset=44
    local.get $l3
    i32.const 32
    i32.store offset=28
    i32.const 0
    local.set $l4
    local.get $l3
    i32.const 0
    i32.store offset=40
    local.get $l3
    local.get $p1
    i32.store offset=36
    local.get $l3
    local.get $p0
    i32.store offset=32
    local.get $l3
    i32.const 0
    i32.store offset=20
    local.get $l3
    i32.const 0
    i32.store offset=12
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              local.get $p2
              i32.load offset=16
              local.tee $l5
              br_if 0 (;@5;)
              local.get $p2
              i32.load offset=12
              local.tee $p0
              i32.eqz
              br_if 1 (;@4;)
              local.get $p2
              i32.load offset=8
              local.set $p1
              local.get $p0
              i32.const 3
              i32.shl
              local.set $l6
              local.get $p0
              i32.const -1
              i32.add
              i32.const 536870911
              i32.and
              i32.const 1
              i32.add
              local.set $l4
              local.get $p2
              i32.load
              local.set $p0
              loop  ;; label = @6
                block  ;; label = @7
                  local.get $p0
                  i32.const 4
                  i32.add
                  i32.load
                  local.tee $l7
                  i32.eqz
                  br_if 0 (;@7;)
                  local.get $l3
                  i32.load offset=32
                  local.get $p0
                  i32.load
                  local.get $l7
                  local.get $l3
                  i32.load offset=36
                  i32.load offset=12
                  call_indirect $T0 (type $t0)
                  br_if 4 (;@3;)
                end
                local.get $p1
                i32.load
                local.get $l3
                i32.const 12
                i32.add
                local.get $p1
                i32.load offset=4
                call_indirect $T0 (type $t1)
                br_if 3 (;@3;)
                local.get $p1
                i32.const 8
                i32.add
                local.set $p1
                local.get $p0
                i32.const 8
                i32.add
                local.set $p0
                local.get $l6
                i32.const -8
                i32.add
                local.tee $l6
                br_if 0 (;@6;)
                br 2 (;@4;)
              end
            end
            local.get $p2
            i32.load offset=20
            local.tee $p1
            i32.eqz
            br_if 0 (;@4;)
            local.get $p1
            i32.const 5
            i32.shl
            local.set $l8
            local.get $p1
            i32.const -1
            i32.add
            i32.const 134217727
            i32.and
            i32.const 1
            i32.add
            local.set $l4
            local.get $p2
            i32.load offset=8
            local.set $l9
            local.get $p2
            i32.load
            local.set $p0
            i32.const 0
            local.set $l6
            loop  ;; label = @5
              block  ;; label = @6
                local.get $p0
                i32.const 4
                i32.add
                i32.load
                local.tee $p1
                i32.eqz
                br_if 0 (;@6;)
                local.get $l3
                i32.load offset=32
                local.get $p0
                i32.load
                local.get $p1
                local.get $l3
                i32.load offset=36
                i32.load offset=12
                call_indirect $T0 (type $t0)
                br_if 3 (;@3;)
              end
              local.get $l3
              local.get $l5
              local.get $l6
              i32.add
              local.tee $p1
              i32.const 16
              i32.add
              i32.load
              i32.store offset=28
              local.get $l3
              local.get $p1
              i32.const 28
              i32.add
              i32.load8_u
              i32.store8 offset=44
              local.get $l3
              local.get $p1
              i32.const 24
              i32.add
              i32.load
              i32.store offset=40
              local.get $p1
              i32.const 12
              i32.add
              i32.load
              local.set $l7
              i32.const 0
              local.set $l10
              i32.const 0
              local.set $l11
              block  ;; label = @6
                block  ;; label = @7
                  block  ;; label = @8
                    local.get $p1
                    i32.const 8
                    i32.add
                    i32.load
                    br_table 1 (;@7;) 0 (;@8;) 2 (;@6;) 1 (;@7;)
                  end
                  local.get $l7
                  i32.const 3
                  i32.shl
                  local.set $l12
                  i32.const 0
                  local.set $l11
                  local.get $l9
                  local.get $l12
                  i32.add
                  local.tee $l12
                  i32.load offset=4
                  br_if 1 (;@6;)
                  local.get $l12
                  i32.load
                  local.set $l7
                end
                i32.const 1
                local.set $l11
              end
              local.get $l3
              local.get $l7
              i32.store offset=16
              local.get $l3
              local.get $l11
              i32.store offset=12
              local.get $p1
              i32.const 4
              i32.add
              i32.load
              local.set $l7
              block  ;; label = @6
                block  ;; label = @7
                  block  ;; label = @8
                    local.get $p1
                    i32.load
                    br_table 1 (;@7;) 0 (;@8;) 2 (;@6;) 1 (;@7;)
                  end
                  local.get $l7
                  i32.const 3
                  i32.shl
                  local.set $l11
                  local.get $l9
                  local.get $l11
                  i32.add
                  local.tee $l11
                  i32.load offset=4
                  br_if 1 (;@6;)
                  local.get $l11
                  i32.load
                  local.set $l7
                end
                i32.const 1
                local.set $l10
              end
              local.get $l3
              local.get $l7
              i32.store offset=24
              local.get $l3
              local.get $l10
              i32.store offset=20
              local.get $l9
              local.get $p1
              i32.const 20
              i32.add
              i32.load
              i32.const 3
              i32.shl
              i32.add
              local.tee $p1
              i32.load
              local.get $l3
              i32.const 12
              i32.add
              local.get $p1
              i32.load offset=4
              call_indirect $T0 (type $t1)
              br_if 2 (;@3;)
              local.get $p0
              i32.const 8
              i32.add
              local.set $p0
              local.get $l8
              local.get $l6
              i32.const 32
              i32.add
              local.tee $l6
              i32.ne
              br_if 0 (;@5;)
            end
          end
          local.get $l4
          local.get $p2
          i32.load offset=4
          i32.ge_u
          br_if 1 (;@2;)
          local.get $l3
          i32.load offset=32
          local.get $p2
          i32.load
          local.get $l4
          i32.const 3
          i32.shl
          i32.add
          local.tee $p1
          i32.load
          local.get $p1
          i32.load offset=4
          local.get $l3
          i32.load offset=36
          i32.load offset=12
          call_indirect $T0 (type $t0)
          i32.eqz
          br_if 1 (;@2;)
        end
        i32.const 1
        local.set $p1
        br 1 (;@1;)
      end
      i32.const 0
      local.set $p1
    end
    local.get $l3
    i32.const 48
    i32.add
    global.set $__stack_pointer
    local.get $p1)
  (func $_ZN4core6result13unwrap_failed17h472431483d5eea7fE (type $t30) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (param $p4 i32)
    (local $l5 i32)
    global.get $__stack_pointer
    i32.const 64
    i32.sub
    local.tee $l5
    global.set $__stack_pointer
    local.get $l5
    local.get $p1
    i32.store offset=12
    local.get $l5
    local.get $p0
    i32.store offset=8
    local.get $l5
    local.get $p3
    i32.store offset=20
    local.get $l5
    local.get $p2
    i32.store offset=16
    local.get $l5
    i32.const 2
    i32.store offset=28
    local.get $l5
    i32.const 1050164
    i32.store offset=24
    local.get $l5
    i64.const 2
    i64.store offset=36 align=4
    local.get $l5
    i32.const 5
    i64.extend_i32_u
    i64.const 32
    i64.shl
    local.get $l5
    i32.const 16
    i32.add
    i64.extend_i32_u
    i64.or
    i64.store offset=56
    local.get $l5
    i32.const 6
    i64.extend_i32_u
    i64.const 32
    i64.shl
    local.get $l5
    i32.const 8
    i32.add
    i64.extend_i32_u
    i64.or
    i64.store offset=48
    local.get $l5
    local.get $l5
    i32.const 48
    i32.add
    i32.store offset=32
    local.get $l5
    i32.const 24
    i32.add
    local.get $p4
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E (type $t16) (param $p0 i32)
    i32.const 1050116
    i32.const 43
    local.get $p0
    call $_ZN4core9panicking5panic17hcaca2598a27ec0fcE
    unreachable)
  (func $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17h9634f975d7713204E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p1
    local.get $p0
    i32.load
    local.get $p0
    i32.load offset=4
    call $_ZN4core3fmt9Formatter3pad17hdad3e25ba05328b0E)
  (func $_ZN42_$LT$$RF$T$u20$as$u20$core..fmt..Debug$GT$3fmt17hbd1c3de5eced27c6E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p0
    i32.load
    local.get $p1
    local.get $p0
    i32.load offset=4
    i32.load offset=12
    call_indirect $T0 (type $t1))
  (func $_ZN4core3fmt9Formatter12pad_integral17h7dae91fc148a1aefE (type $t31) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (param $p4 i32) (param $p5 i32) (result i32)
    (local $l6 i32) (local $l7 i32) (local $l8 i32) (local $l9 i32) (local $l10 i32) (local $l11 i32) (local $l12 i32)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p1
        br_if 0 (;@2;)
        local.get $p5
        i32.const 1
        i32.add
        local.set $l6
        local.get $p0
        i32.load offset=28
        local.set $l7
        i32.const 45
        local.set $l8
        br 1 (;@1;)
      end
      i32.const 43
      i32.const 1114112
      local.get $p0
      i32.load offset=28
      local.tee $l7
      i32.const 1
      i32.and
      local.tee $p1
      select
      local.set $l8
      local.get $p1
      local.get $p5
      i32.add
      local.set $l6
    end
    block  ;; label = @1
      block  ;; label = @2
        local.get $l7
        i32.const 4
        i32.and
        br_if 0 (;@2;)
        i32.const 0
        local.set $p2
        br 1 (;@1;)
      end
      block  ;; label = @2
        block  ;; label = @3
          local.get $p3
          i32.const 16
          i32.lt_u
          br_if 0 (;@3;)
          local.get $p2
          local.get $p3
          call $_ZN4core3str5count14do_count_chars17h5612f5cea15e8f3fE
          local.set $p1
          br 1 (;@2;)
        end
        block  ;; label = @3
          local.get $p3
          br_if 0 (;@3;)
          i32.const 0
          local.set $p1
          br 1 (;@2;)
        end
        local.get $p3
        i32.const 3
        i32.and
        local.set $l9
        block  ;; label = @3
          block  ;; label = @4
            local.get $p3
            i32.const 4
            i32.ge_u
            br_if 0 (;@4;)
            i32.const 0
            local.set $p1
            i32.const 0
            local.set $l10
            br 1 (;@3;)
          end
          local.get $p3
          i32.const 12
          i32.and
          local.set $l11
          i32.const 0
          local.set $p1
          i32.const 0
          local.set $l10
          loop  ;; label = @4
            local.get $p1
            local.get $p2
            local.get $l10
            i32.add
            local.tee $l12
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.get $l12
            i32.const 1
            i32.add
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.get $l12
            i32.const 2
            i32.add
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.get $l12
            i32.const 3
            i32.add
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.set $p1
            local.get $l11
            local.get $l10
            i32.const 4
            i32.add
            local.tee $l10
            i32.ne
            br_if 0 (;@4;)
          end
        end
        local.get $l9
        i32.eqz
        br_if 0 (;@2;)
        local.get $p2
        local.get $l10
        i32.add
        local.set $l12
        loop  ;; label = @3
          local.get $p1
          local.get $l12
          i32.load8_s
          i32.const -65
          i32.gt_s
          i32.add
          local.set $p1
          local.get $l12
          i32.const 1
          i32.add
          local.set $l12
          local.get $l9
          i32.const -1
          i32.add
          local.tee $l9
          br_if 0 (;@3;)
        end
      end
      local.get $p1
      local.get $l6
      i32.add
      local.set $l6
    end
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i32.load
        br_if 0 (;@2;)
        i32.const 1
        local.set $p1
        local.get $p0
        i32.load offset=20
        local.tee $l12
        local.get $p0
        i32.load offset=24
        local.tee $l10
        local.get $l8
        local.get $p2
        local.get $p3
        call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
        br_if 1 (;@1;)
        local.get $l12
        local.get $p4
        local.get $p5
        local.get $l10
        i32.load offset=12
        call_indirect $T0 (type $t0)
        return
      end
      block  ;; label = @2
        local.get $p0
        i32.load offset=4
        local.tee $l9
        local.get $l6
        i32.gt_u
        br_if 0 (;@2;)
        i32.const 1
        local.set $p1
        local.get $p0
        i32.load offset=20
        local.tee $l12
        local.get $p0
        i32.load offset=24
        local.tee $l10
        local.get $l8
        local.get $p2
        local.get $p3
        call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
        br_if 1 (;@1;)
        local.get $l12
        local.get $p4
        local.get $p5
        local.get $l10
        i32.load offset=12
        call_indirect $T0 (type $t0)
        return
      end
      block  ;; label = @2
        local.get $l7
        i32.const 8
        i32.and
        i32.eqz
        br_if 0 (;@2;)
        local.get $p0
        i32.load offset=16
        local.set $l11
        local.get $p0
        i32.const 48
        i32.store offset=16
        local.get $p0
        i32.load8_u offset=32
        local.set $l7
        i32.const 1
        local.set $p1
        local.get $p0
        i32.const 1
        i32.store8 offset=32
        local.get $p0
        i32.load offset=20
        local.tee $l12
        local.get $p0
        i32.load offset=24
        local.tee $l10
        local.get $l8
        local.get $p2
        local.get $p3
        call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
        br_if 1 (;@1;)
        local.get $l9
        local.get $l6
        i32.sub
        i32.const 1
        i32.add
        local.set $p1
        block  ;; label = @3
          loop  ;; label = @4
            local.get $p1
            i32.const -1
            i32.add
            local.tee $p1
            i32.eqz
            br_if 1 (;@3;)
            local.get $l12
            i32.const 48
            local.get $l10
            i32.load offset=16
            call_indirect $T0 (type $t1)
            i32.eqz
            br_if 0 (;@4;)
          end
          i32.const 1
          return
        end
        i32.const 1
        local.set $p1
        local.get $l12
        local.get $p4
        local.get $p5
        local.get $l10
        i32.load offset=12
        call_indirect $T0 (type $t0)
        br_if 1 (;@1;)
        local.get $p0
        local.get $l7
        i32.store8 offset=32
        local.get $p0
        local.get $l11
        i32.store offset=16
        i32.const 0
        local.set $p1
        br 1 (;@1;)
      end
      local.get $l9
      local.get $l6
      i32.sub
      local.set $l6
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            local.get $p0
            i32.load8_u offset=32
            local.tee $p1
            br_table 2 (;@2;) 0 (;@4;) 1 (;@3;) 0 (;@4;) 2 (;@2;)
          end
          local.get $l6
          local.set $p1
          i32.const 0
          local.set $l6
          br 1 (;@2;)
        end
        local.get $l6
        i32.const 1
        i32.shr_u
        local.set $p1
        local.get $l6
        i32.const 1
        i32.add
        i32.const 1
        i32.shr_u
        local.set $l6
      end
      local.get $p1
      i32.const 1
      i32.add
      local.set $p1
      local.get $p0
      i32.load offset=16
      local.set $l9
      local.get $p0
      i32.load offset=24
      local.set $l12
      local.get $p0
      i32.load offset=20
      local.set $l10
      block  ;; label = @2
        loop  ;; label = @3
          local.get $p1
          i32.const -1
          i32.add
          local.tee $p1
          i32.eqz
          br_if 1 (;@2;)
          local.get $l10
          local.get $l9
          local.get $l12
          i32.load offset=16
          call_indirect $T0 (type $t1)
          i32.eqz
          br_if 0 (;@3;)
        end
        i32.const 1
        return
      end
      i32.const 1
      local.set $p1
      local.get $l10
      local.get $l12
      local.get $l8
      local.get $p2
      local.get $p3
      call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
      br_if 0 (;@1;)
      local.get $l10
      local.get $p4
      local.get $p5
      local.get $l12
      i32.load offset=12
      call_indirect $T0 (type $t0)
      br_if 0 (;@1;)
      i32.const 0
      local.set $p1
      loop  ;; label = @2
        block  ;; label = @3
          local.get $l6
          local.get $p1
          i32.ne
          br_if 0 (;@3;)
          local.get $l6
          local.get $l6
          i32.lt_u
          return
        end
        local.get $p1
        i32.const 1
        i32.add
        local.set $p1
        local.get $l10
        local.get $l9
        local.get $l12
        i32.load offset=16
        call_indirect $T0 (type $t1)
        i32.eqz
        br_if 0 (;@2;)
      end
      local.get $p1
      i32.const -1
      i32.add
      local.get $l6
      i32.lt_u
      return
    end
    local.get $p1)
  (func $_ZN4core3str5count14do_count_chars17h5612f5cea15e8f3fE (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32) (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32) (local $l7 i32) (local $l8 i32) (local $l9 i32)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p1
        local.get $p0
        i32.const 3
        i32.add
        i32.const -4
        i32.and
        local.tee $l2
        local.get $p0
        i32.sub
        local.tee $l3
        i32.lt_u
        br_if 0 (;@2;)
        local.get $p1
        local.get $l3
        i32.sub
        local.tee $l4
        i32.const 4
        i32.lt_u
        br_if 0 (;@2;)
        local.get $l4
        i32.const 3
        i32.and
        local.set $l5
        i32.const 0
        local.set $l6
        i32.const 0
        local.set $p1
        block  ;; label = @3
          local.get $l2
          local.get $p0
          i32.eq
          local.tee $l7
          br_if 0 (;@3;)
          i32.const 0
          local.set $p1
          block  ;; label = @4
            block  ;; label = @5
              local.get $p0
              local.get $l2
              i32.sub
              local.tee $l8
              i32.const -4
              i32.le_u
              br_if 0 (;@5;)
              i32.const 0
              local.set $l9
              br 1 (;@4;)
            end
            i32.const 0
            local.set $l9
            loop  ;; label = @5
              local.get $p1
              local.get $p0
              local.get $l9
              i32.add
              local.tee $l2
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.get $l2
              i32.const 1
              i32.add
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.get $l2
              i32.const 2
              i32.add
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.get $l2
              i32.const 3
              i32.add
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.set $p1
              local.get $l9
              i32.const 4
              i32.add
              local.tee $l9
              br_if 0 (;@5;)
            end
          end
          local.get $l7
          br_if 0 (;@3;)
          local.get $p0
          local.get $l9
          i32.add
          local.set $l2
          loop  ;; label = @4
            local.get $p1
            local.get $l2
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.set $p1
            local.get $l2
            i32.const 1
            i32.add
            local.set $l2
            local.get $l8
            i32.const 1
            i32.add
            local.tee $l8
            br_if 0 (;@4;)
          end
        end
        local.get $p0
        local.get $l3
        i32.add
        local.set $l9
        block  ;; label = @3
          local.get $l5
          i32.eqz
          br_if 0 (;@3;)
          local.get $l9
          local.get $l4
          i32.const -4
          i32.and
          i32.add
          local.tee $l2
          i32.load8_s
          i32.const -65
          i32.gt_s
          local.set $l6
          local.get $l5
          i32.const 1
          i32.eq
          br_if 0 (;@3;)
          local.get $l6
          local.get $l2
          i32.load8_s offset=1
          i32.const -65
          i32.gt_s
          i32.add
          local.set $l6
          local.get $l5
          i32.const 2
          i32.eq
          br_if 0 (;@3;)
          local.get $l6
          local.get $l2
          i32.load8_s offset=2
          i32.const -65
          i32.gt_s
          i32.add
          local.set $l6
        end
        local.get $l4
        i32.const 2
        i32.shr_u
        local.set $l3
        local.get $l6
        local.get $p1
        i32.add
        local.set $l8
        loop  ;; label = @3
          local.get $l9
          local.set $l4
          local.get $l3
          i32.eqz
          br_if 2 (;@1;)
          local.get $l3
          i32.const 192
          local.get $l3
          i32.const 192
          i32.lt_u
          select
          local.tee $l6
          i32.const 3
          i32.and
          local.set $l7
          local.get $l6
          i32.const 2
          i32.shl
          local.set $l5
          i32.const 0
          local.set $l2
          block  ;; label = @4
            local.get $l3
            i32.const 4
            i32.lt_u
            br_if 0 (;@4;)
            local.get $l4
            local.get $l5
            i32.const 1008
            i32.and
            i32.add
            local.set $p0
            i32.const 0
            local.set $l2
            local.get $l4
            local.set $p1
            loop  ;; label = @5
              local.get $p1
              i32.load offset=12
              local.tee $l9
              i32.const -1
              i32.xor
              i32.const 7
              i32.shr_u
              local.get $l9
              i32.const 6
              i32.shr_u
              i32.or
              i32.const 16843009
              i32.and
              local.get $p1
              i32.load offset=8
              local.tee $l9
              i32.const -1
              i32.xor
              i32.const 7
              i32.shr_u
              local.get $l9
              i32.const 6
              i32.shr_u
              i32.or
              i32.const 16843009
              i32.and
              local.get $p1
              i32.load offset=4
              local.tee $l9
              i32.const -1
              i32.xor
              i32.const 7
              i32.shr_u
              local.get $l9
              i32.const 6
              i32.shr_u
              i32.or
              i32.const 16843009
              i32.and
              local.get $p1
              i32.load
              local.tee $l9
              i32.const -1
              i32.xor
              i32.const 7
              i32.shr_u
              local.get $l9
              i32.const 6
              i32.shr_u
              i32.or
              i32.const 16843009
              i32.and
              local.get $l2
              i32.add
              i32.add
              i32.add
              i32.add
              local.set $l2
              local.get $p1
              i32.const 16
              i32.add
              local.tee $p1
              local.get $p0
              i32.ne
              br_if 0 (;@5;)
            end
          end
          local.get $l3
          local.get $l6
          i32.sub
          local.set $l3
          local.get $l4
          local.get $l5
          i32.add
          local.set $l9
          local.get $l2
          i32.const 8
          i32.shr_u
          i32.const 16711935
          i32.and
          local.get $l2
          i32.const 16711935
          i32.and
          i32.add
          i32.const 65537
          i32.mul
          i32.const 16
          i32.shr_u
          local.get $l8
          i32.add
          local.set $l8
          local.get $l7
          i32.eqz
          br_if 0 (;@3;)
        end
        local.get $l4
        local.get $l6
        i32.const 252
        i32.and
        i32.const 2
        i32.shl
        i32.add
        local.tee $l2
        i32.load
        local.tee $p1
        i32.const -1
        i32.xor
        i32.const 7
        i32.shr_u
        local.get $p1
        i32.const 6
        i32.shr_u
        i32.or
        i32.const 16843009
        i32.and
        local.set $p1
        block  ;; label = @3
          local.get $l7
          i32.const 1
          i32.eq
          br_if 0 (;@3;)
          local.get $l2
          i32.load offset=4
          local.tee $l9
          i32.const -1
          i32.xor
          i32.const 7
          i32.shr_u
          local.get $l9
          i32.const 6
          i32.shr_u
          i32.or
          i32.const 16843009
          i32.and
          local.get $p1
          i32.add
          local.set $p1
          local.get $l7
          i32.const 2
          i32.eq
          br_if 0 (;@3;)
          local.get $l2
          i32.load offset=8
          local.tee $l2
          i32.const -1
          i32.xor
          i32.const 7
          i32.shr_u
          local.get $l2
          i32.const 6
          i32.shr_u
          i32.or
          i32.const 16843009
          i32.and
          local.get $p1
          i32.add
          local.set $p1
        end
        local.get $p1
        i32.const 8
        i32.shr_u
        i32.const 459007
        i32.and
        local.get $p1
        i32.const 16711935
        i32.and
        i32.add
        i32.const 65537
        i32.mul
        i32.const 16
        i32.shr_u
        local.get $l8
        i32.add
        return
      end
      block  ;; label = @2
        local.get $p1
        br_if 0 (;@2;)
        i32.const 0
        return
      end
      local.get $p1
      i32.const 3
      i32.and
      local.set $l9
      block  ;; label = @2
        block  ;; label = @3
          local.get $p1
          i32.const 4
          i32.ge_u
          br_if 0 (;@3;)
          i32.const 0
          local.set $l8
          i32.const 0
          local.set $l2
          br 1 (;@2;)
        end
        local.get $p1
        i32.const -4
        i32.and
        local.set $l3
        i32.const 0
        local.set $l8
        i32.const 0
        local.set $l2
        loop  ;; label = @3
          local.get $l8
          local.get $p0
          local.get $l2
          i32.add
          local.tee $p1
          i32.load8_s
          i32.const -65
          i32.gt_s
          i32.add
          local.get $p1
          i32.const 1
          i32.add
          i32.load8_s
          i32.const -65
          i32.gt_s
          i32.add
          local.get $p1
          i32.const 2
          i32.add
          i32.load8_s
          i32.const -65
          i32.gt_s
          i32.add
          local.get $p1
          i32.const 3
          i32.add
          i32.load8_s
          i32.const -65
          i32.gt_s
          i32.add
          local.set $l8
          local.get $l3
          local.get $l2
          i32.const 4
          i32.add
          local.tee $l2
          i32.ne
          br_if 0 (;@3;)
        end
      end
      local.get $l9
      i32.eqz
      br_if 0 (;@1;)
      local.get $p0
      local.get $l2
      i32.add
      local.set $p1
      loop  ;; label = @2
        local.get $l8
        local.get $p1
        i32.load8_s
        i32.const -65
        i32.gt_s
        i32.add
        local.set $l8
        local.get $p1
        i32.const 1
        i32.add
        local.set $p1
        local.get $l9
        i32.const -1
        i32.add
        local.tee $l9
        br_if 0 (;@2;)
      end
    end
    local.get $l8)
  (func $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E (type $t32) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (param $p4 i32) (result i32)
    (local $l5 i32)
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p2
          i32.const 1114112
          i32.eq
          br_if 0 (;@3;)
          i32.const 1
          local.set $l5
          local.get $p0
          local.get $p2
          local.get $p1
          i32.load offset=16
          call_indirect $T0 (type $t1)
          br_if 1 (;@2;)
        end
        local.get $p3
        br_if 1 (;@1;)
        i32.const 0
        local.set $l5
      end
      local.get $l5
      return
    end
    local.get $p0
    local.get $p3
    local.get $p4
    local.get $p1
    i32.load offset=12
    call_indirect $T0 (type $t0))
  (func $_ZN4core3fmt9Formatter9write_str17h89c4071b72e49099E (type $t0) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    local.get $p0
    i32.load offset=20
    local.get $p1
    local.get $p2
    local.get $p0
    i32.load offset=24
    i32.load offset=12
    call_indirect $T0 (type $t0))
  (func $_ZN42_$LT$str$u20$as$u20$core..fmt..Display$GT$3fmt17ha62171cbd2687de4E (type $t0) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    local.get $p2
    local.get $p0
    local.get $p1
    call $_ZN4core3fmt9Formatter3pad17hdad3e25ba05328b0E)
  (func $_ZN4core9panicking11panic_const24panic_const_sub_overflow17hddb96f4b6b3b1af0E (type $t16) (param $p0 i32)
    (local $l1 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    i32.const 0
    i32.store offset=24
    local.get $l1
    i32.const 1
    i32.store offset=12
    local.get $l1
    i32.const 1050108
    i32.store offset=8
    local.get $l1
    i64.const 4
    i64.store offset=16 align=4
    local.get $l1
    i32.const 8
    i32.add
    local.get $p0
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core3fmt3num3imp7fmt_u6417hdb0013e0ceafa0e4E (type $t33) (param $p0 i64) (param $p1 i32) (param $p2 i32) (result i32)
    (local $l3 i32) (local $l4 i32) (local $l5 i64) (local $l6 i32) (local $l7 i32) (local $l8 i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    i32.const 39
    local.set $l4
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i64.const 10000
        i64.ge_u
        br_if 0 (;@2;)
        local.get $p0
        local.set $l5
        br 1 (;@1;)
      end
      i32.const 39
      local.set $l4
      loop  ;; label = @2
        local.get $l3
        i32.const 9
        i32.add
        local.get $l4
        i32.add
        local.tee $l6
        i32.const -4
        i32.add
        local.get $p0
        local.get $p0
        i64.const 10000
        i64.div_u
        local.tee $l5
        i64.const 10000
        i64.mul
        i64.sub
        i32.wrap_i64
        local.tee $l7
        i32.const 65535
        i32.and
        i32.const 100
        i32.div_u
        local.tee $l8
        i32.const 1
        i32.shl
        i32.const 1050180
        i32.add
        i32.load16_u align=1
        i32.store16 align=1
        local.get $l6
        i32.const -2
        i32.add
        local.get $l7
        local.get $l8
        i32.const 100
        i32.mul
        i32.sub
        i32.const 65535
        i32.and
        i32.const 1
        i32.shl
        i32.const 1050180
        i32.add
        i32.load16_u align=1
        i32.store16 align=1
        local.get $l4
        i32.const -4
        i32.add
        local.set $l4
        local.get $p0
        i64.const 99999999
        i64.gt_u
        local.set $l6
        local.get $l5
        local.set $p0
        local.get $l6
        br_if 0 (;@2;)
      end
    end
    block  ;; label = @1
      local.get $l5
      i32.wrap_i64
      local.tee $l6
      i32.const 99
      i32.le_u
      br_if 0 (;@1;)
      local.get $l3
      i32.const 9
      i32.add
      local.get $l4
      i32.const -2
      i32.add
      local.tee $l4
      i32.add
      local.get $l5
      i32.wrap_i64
      local.tee $l6
      local.get $l6
      i32.const 65535
      i32.and
      i32.const 100
      i32.div_u
      local.tee $l6
      i32.const 100
      i32.mul
      i32.sub
      i32.const 65535
      i32.and
      i32.const 1
      i32.shl
      i32.const 1050180
      i32.add
      i32.load16_u align=1
      i32.store16 align=1
    end
    block  ;; label = @1
      block  ;; label = @2
        local.get $l6
        i32.const 10
        i32.lt_u
        br_if 0 (;@2;)
        local.get $l3
        i32.const 9
        i32.add
        local.get $l4
        i32.const -2
        i32.add
        local.tee $l4
        i32.add
        local.get $l6
        i32.const 1
        i32.shl
        i32.const 1050180
        i32.add
        i32.load16_u align=1
        i32.store16 align=1
        br 1 (;@1;)
      end
      local.get $l3
      i32.const 9
      i32.add
      local.get $l4
      i32.const -1
      i32.add
      local.tee $l4
      i32.add
      local.get $l6
      i32.const 48
      i32.or
      i32.store8
    end
    local.get $p2
    local.get $p1
    i32.const 1
    i32.const 0
    local.get $l3
    i32.const 9
    i32.add
    local.get $l4
    i32.add
    i32.const 39
    local.get $l4
    i32.sub
    call $_ZN4core3fmt9Formatter12pad_integral17h7dae91fc148a1aefE
    local.set $l4
    local.get $l3
    i32.const 48
    i32.add
    global.set $__stack_pointer
    local.get $l4)
  (func $_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i32$GT$3fmt17hd6308d8453dcc3baE (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32)
    local.get $p0
    i32.load
    local.tee $p0
    local.get $p0
    i32.const 31
    i32.shr_s
    local.tee $l2
    i32.xor
    local.get $l2
    i32.sub
    i64.extend_i32_u
    local.get $p0
    i32.const -1
    i32.xor
    i32.const 31
    i32.shr_u
    local.get $p1
    call $_ZN4core3fmt3num3imp7fmt_u6417hdb0013e0ceafa0e4E)
  (func $_ZN17compiler_builtins3mem6memcpy17h4d1b3bf0b8e43c13E (type $t0) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32) (local $l7 i32) (local $l8 i32) (local $l9 i32) (local $l10 i32)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p2
        i32.const 16
        i32.ge_u
        br_if 0 (;@2;)
        local.get $p0
        local.set $l3
        br 1 (;@1;)
      end
      local.get $p0
      i32.const 0
      local.get $p0
      i32.sub
      i32.const 3
      i32.and
      local.tee $l4
      i32.add
      local.set $l5
      block  ;; label = @2
        local.get $l4
        i32.eqz
        br_if 0 (;@2;)
        local.get $p0
        local.set $l3
        local.get $p1
        local.set $l6
        loop  ;; label = @3
          local.get $l3
          local.get $l6
          i32.load8_u
          i32.store8
          local.get $l6
          i32.const 1
          i32.add
          local.set $l6
          local.get $l3
          i32.const 1
          i32.add
          local.tee $l3
          local.get $l5
          i32.lt_u
          br_if 0 (;@3;)
        end
      end
      local.get $l5
      local.get $p2
      local.get $l4
      i32.sub
      local.tee $l7
      i32.const -4
      i32.and
      local.tee $l8
      i32.add
      local.set $l3
      block  ;; label = @2
        block  ;; label = @3
          local.get $p1
          local.get $l4
          i32.add
          local.tee $l9
          i32.const 3
          i32.and
          i32.eqz
          br_if 0 (;@3;)
          local.get $l8
          i32.const 1
          i32.lt_s
          br_if 1 (;@2;)
          local.get $l9
          i32.const 3
          i32.shl
          local.tee $l6
          i32.const 24
          i32.and
          local.set $p2
          local.get $l9
          i32.const -4
          i32.and
          local.tee $l10
          i32.const 4
          i32.add
          local.set $p1
          i32.const 0
          local.get $l6
          i32.sub
          i32.const 24
          i32.and
          local.set $l4
          local.get $l10
          i32.load
          local.set $l6
          loop  ;; label = @4
            local.get $l5
            local.get $l6
            local.get $p2
            i32.shr_u
            local.get $p1
            i32.load
            local.tee $l6
            local.get $l4
            i32.shl
            i32.or
            i32.store
            local.get $p1
            i32.const 4
            i32.add
            local.set $p1
            local.get $l5
            i32.const 4
            i32.add
            local.tee $l5
            local.get $l3
            i32.lt_u
            br_if 0 (;@4;)
            br 2 (;@2;)
          end
        end
        local.get $l8
        i32.const 1
        i32.lt_s
        br_if 0 (;@2;)
        local.get $l9
        local.set $p1
        loop  ;; label = @3
          local.get $l5
          local.get $p1
          i32.load
          i32.store
          local.get $p1
          i32.const 4
          i32.add
          local.set $p1
          local.get $l5
          i32.const 4
          i32.add
          local.tee $l5
          local.get $l3
          i32.lt_u
          br_if 0 (;@3;)
        end
      end
      local.get $l7
      i32.const 3
      i32.and
      local.set $p2
      local.get $l9
      local.get $l8
      i32.add
      local.set $p1
    end
    block  ;; label = @1
      local.get $p2
      i32.eqz
      br_if 0 (;@1;)
      local.get $l3
      local.get $p2
      i32.add
      local.set $l5
      loop  ;; label = @2
        local.get $l3
        local.get $p1
        i32.load8_u
        i32.store8
        local.get $p1
        i32.const 1
        i32.add
        local.set $p1
        local.get $l3
        i32.const 1
        i32.add
        local.tee $l3
        local.get $l5
        i32.lt_u
        br_if 0 (;@2;)
      end
    end
    local.get $p0)
  (func $memcpy (type $t0) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    local.get $p0
    local.get $p1
    local.get $p2
    call $_ZN17compiler_builtins3mem6memcpy17h4d1b3bf0b8e43c13E)
  (table $T0 7 7 funcref)
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1050380))
  (global $__heap_base i32 (i32.const 1050384))
  (export "memory" (memory $memory))
  (export "deposit" (func $deposit))
  (export "claim" (func $claim))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (elem $e0 (i32.const 1) func $_ZN77_$LT$soroban_env_common..val..ConversionError$u20$as$u20$core..fmt..Debug$GT$3fmt17h436be35266574685E $_ZN69_$LT$soroban_env_common..error..Error$u20$as$u20$core..fmt..Debug$GT$3fmt17h6121ab0f52dd5078E $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17h9c75e7f5eb72e75dE $_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i32$GT$3fmt17hd6308d8453dcc3baE $_ZN42_$LT$$RF$T$u20$as$u20$core..fmt..Debug$GT$3fmt17hbd1c3de5eced27c6E $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17h9634f975d7713204E)
  (data $.rodata (i32.const 1048576) "\00Init\00\00\00\01\00\10\00\04\00\00\00src/lib.rsBalance\00\00\00\1a\00\10\00\07\00\00\00BeforeAfter\00,\00\10\00\06\00\00\002\00\10\00\05\00\00\00,\00\10\00\06\00\00\002\00\10\00\05\00\00\00kindtimestamp\00\00\00X\00\10\00\04\00\00\00\5c\00\10\00\09\00\00\00amountclaimantstime_boundtoken\00\00x\00\10\00\06\00\00\00~\00\10\00\09\00\00\00\87\00\10\00\0a\00\00\00\91\00\10\00\05\00\00\00\01contract has been already initialized\00\00\b9\00\10\00%\00\00\00\10\00\10\00\0a\00\00\00Q\00\00\00\0d\00\00\00too many claimants\00\00\f8\00\10\00\12\00\00\00\10\00\10\00\0a\00\00\00N\00\00\00\0d\00\00\00need more than 0 claimants\00\00$\01\10\00\1a\00\00\00\10\00\10\00\0a\00\00\00K\00\00\00\0d\00\00\00\10\00\10\00\0a\00\00\00o\00\00\00?\00\00\00time predicate is not fulfilled\00h\01\10\00\1f\00\00\00\10\00\10\00\0a\00\00\00r\00\00\00\0d\00\00\00claimant is not allowed to claim this balance\00\00\00\a0\01\10\00-\00\00\00\10\00\10\00\0a\00\00\00w\00\00\00\0d\00\00\00\10\00\10\00\0a\00\00\00\86\00\00\00\1b\00\00\00claimed amount greater than balance\00\f8\01\10\00#\00\00\00\10\00\10\00\0a\00\00\00{\00\00\00\0d\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00called `Result::unwrap()` on an `Err` value\00\00\00\00\00\08\00\00\00\08\00\00\00\02\00\00\00ConversionError/Users/johannesspath/.cargo/registry/src/index.crates.io-6f17d22bba15001f/soroban-sdk-21.6.0/src/env.rs\00\00\8f\02\10\00g\00\00\00\84\01\00\00\0e\00\00\00/Users/johannesspath/.cargo/registry/src/index.crates.io-6f17d22bba15001f/soroban-sdk-21.6.0/src/ledger.rs\00\00\08\03\10\00j\00\00\00[\00\00\00\0e\00\00\00/Users/johannesspath/.cargo/registry/src/index.crates.io-6f17d22bba15001f/soroban-sdk-21.6.0/src/vec.rs\00\84\03\10\00g\00\00\00\e7\03\00\00\09\00\00\00\00\00\00\00\0e\b7\ba\e2\b3y\e7\00ArithDomainIndexBoundsInvalidInputMissingValueExistingValueExceededLimitInvalidActionInternalErrorUnexpectedTypeUnexpectedSizeContractWasmVmContextStorageObjectCryptoEventsBudgetValueAuthError(, )\c3\04\10\00\06\00\00\00\c9\04\10\00\02\00\00\00\cb\04\10\00\01\00\00\00, #\00\c3\04\10\00\06\00\00\00\e4\04\10\00\03\00\00\00\cb\04\10\00\01\00\00\00Error(#\00\00\05\10\00\07\00\00\00\c9\04\10\00\02\00\00\00\cb\04\10\00\01\00\00\00\00\05\10\00\07\00\00\00\e4\04\10\00\03\00\00\00\cb\04\10\00\01\00\00\00\0b\00\00\00\0b\00\00\00\0c\00\00\00\0c\00\00\00\0d\00\00\00\0d\00\00\00\0d\00\00\00\0d\00\00\00\0e\00\00\00\0e\00\00\00\08\04\10\00\13\04\10\00\1e\04\10\00*\04\10\006\04\10\00C\04\10\00P\04\10\00]\04\10\00j\04\10\00x\04\10\00\08\00\00\00\06\00\00\00\07\00\00\00\07\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\05\00\00\00\04\00\00\00\86\04\10\00\8e\04\10\00\94\04\10\00\9b\04\10\00\a2\04\10\00\a8\04\10\00\ae\04\10\00\b4\04\10\00\ba\04\10\00\bf\04\10\00attempt to subtract with overflow\00\00\00\d8\05\10\00!\00\00\00called `Option::unwrap()` on a `None` value: \00\00\00\01\00\00\00\00\00\00\00/\06\10\00\02\00\00\0000010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899"))
