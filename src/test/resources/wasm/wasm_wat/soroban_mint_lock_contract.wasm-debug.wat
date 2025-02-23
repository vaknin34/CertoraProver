(module $soroban_mint_lock_contract.wasm
  (type $t0 (func (param i64 i64) (result i64)))
  (type $t1 (func (param i64) (result i64)))
  (type $t2 (func (param i64 i64 i64) (result i64)))
  (type $t3 (func (param i64 i64 i64 i64) (result i64)))
  (type $t4 (func (result i64)))
  (type $t5 (func (param i32 i32)))
  (type $t6 (func (param i32) (result i64)))
  (type $t7 (func (param i64 i64) (result i32)))
  (type $t8 (func (param i32 i64)))
  (type $t9 (func (param i32)))
  (type $t10 (func (param i64 i32 i32 i32 i32)))
  (type $t11 (func (param i32 i32) (result i64)))
  (type $t12 (func (param i64 i64 i32) (result i64)))
  (type $t13 (func (param i32 i32 i32 i32) (result i64)))
  (type $t14 (func (result i32)))
  (type $t15 (func))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E (type $t0)))
  (import "a" "0" (func $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE (type $t1)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E (type $t2)))
  (import "a" "_" (func $_ZN17soroban_env_guest5guest7address21require_auth_for_args17h6ce4b5b084351056E (type $t0)))
  (import "x" "0" (func $_ZN17soroban_env_guest5guest7context7obj_cmp17h189bc77d88b5cf98E (type $t0)))
  (import "l" "7" (func $_ZN17soroban_env_guest5guest6ledger24extend_contract_data_ttl17hfe78b0ca805be00cE (type $t3)))
  (import "d" "_" (func $_ZN17soroban_env_guest5guest4call4call17he38ff75d18335ef7E (type $t2)))
  (import "i" "8" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_hi6417h96047db195ed49dfE (type $t1)))
  (import "i" "7" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_lo6417hda737eee8cb86207E (type $t1)))
  (import "i" "6" (func $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17ha9df624d96cf2a1dE (type $t0)))
  (import "b" "j" (func $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h65f4c5e4b5b0b386E (type $t0)))
  (import "m" "9" (func $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17h999916ef23111b0dE (type $t2)))
  (import "m" "a" (func $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h15a7786289874722E (type $t3)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE (type $t0)))
  (import "x" "3" (func $_ZN17soroban_env_guest5guest7context19get_ledger_sequence17h997670b190a8871eE (type $t4)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE (type $t0)))
  (func $_ZN11soroban_sdk7storage10Persistent3get17hd5af3c7d74ebed2cE (type $t5) (param $p0 i32) (param $p1 i32)
    (local $l2 i32) (local $l3 i64) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    i64.const 0
    local.set $l3
    block  ;; label = @1
      block  ;; label = @2
        local.get $p1
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h963cbcfd3e9f50b8E
        local.tee $l4
        i64.const 1
        call $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE
        i32.eqz
        br_if 0 (;@2;)
        local.get $l2
        local.get $l4
        i64.const 1
        call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E
        call $_ZN160_$LT$soroban_mint_lock_contract..MinterConfig$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h4a0ff91a26aece47E
        local.get $l2
        i64.load
        i64.eqz
        i32.eqz
        br_if 1 (;@1;)
        local.get $l2
        i32.load offset=24
        local.set $p1
        local.get $l2
        i64.load offset=8
        local.set $l3
        local.get $p0
        i32.const 16
        i32.add
        local.get $l2
        i32.const 16
        i32.add
        i64.load
        i64.store
        local.get $p0
        local.get $l3
        i64.store offset=8
        local.get $p0
        local.get $p1
        i32.store offset=24
        i64.const 1
        local.set $l3
      end
      local.get $p0
      local.get $l3
      i64.store
      local.get $l2
      i32.const 32
      i32.add
      global.set $__stack_pointer
      return
    end
    unreachable
    unreachable)
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h963cbcfd3e9f50b8E (type $t6) (param $p0 i32) (result i64)
    (local $l1 i32) (local $l2 i64) (local $l3 i64) (local $l4 i64) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            local.get $p0
            i32.load
            br_table 0 (;@4;) 1 (;@3;) 2 (;@2;) 0 (;@4;)
          end
          local.get $l1
          i32.const 1048576
          i32.const 5
          call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
          i64.store offset=8
          local.get $l1
          i32.const 8
          i32.add
          i32.const 1
          call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf881b9c95e3d1d8eE
          local.set $l2
          br 2 (;@1;)
        end
        i32.const 1048581
        i32.const 6
        call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
        local.set $l2
        local.get $p0
        i64.load offset=8
        local.set $l3
        local.get $l1
        local.get $p0
        i64.load offset=16
        i64.store offset=24
        local.get $l1
        local.get $l3
        i64.store offset=16
        local.get $l1
        local.get $l2
        i64.store offset=8
        local.get $l1
        i32.const 8
        i32.add
        i32.const 3
        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf881b9c95e3d1d8eE
        local.set $l2
        br 1 (;@1;)
      end
      i32.const 1048587
      i32.const 11
      call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
      local.set $l2
      local.get $p0
      i64.load32_u offset=4
      local.set $l3
      local.get $p0
      i64.load32_u offset=8
      local.set $l4
      local.get $p0
      i64.load offset=16
      local.set $l5
      local.get $l1
      local.get $p0
      i64.load offset=24
      i64.store offset=24
      local.get $l1
      local.get $l5
      i64.store offset=16
      local.get $l1
      local.get $l2
      i64.store offset=8
      local.get $l1
      local.get $l4
      i64.const 32
      i64.shl
      i64.const 4
      i64.or
      i64.store offset=40
      local.get $l1
      local.get $l3
      i64.const 32
      i64.shl
      i64.const 4
      i64.or
      i64.store offset=32
      local.get $l1
      i32.const 8
      i32.add
      i32.const 5
      call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf881b9c95e3d1d8eE
      local.set $l2
    end
    local.get $l1
    i32.const 48
    i32.add
    global.set $__stack_pointer
    local.get $l2)
  (func $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE (type $t7) (param $p0 i64) (param $p1 i64) (result i32)
    local.get $p0
    local.get $p1
    call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE
    i64.const 1
    i64.eq)
  (func $_ZN160_$LT$soroban_mint_lock_contract..MinterConfig$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h4a0ff91a26aece47E (type $t8) (param $p0 i32) (param $p1 i64)
    (local $l2 i32) (local $l3 i32) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    i32.const 0
    local.set $l3
    block  ;; label = @1
      loop  ;; label = @2
        local.get $l3
        i32.const 16
        i32.eq
        br_if 1 (;@1;)
        local.get $l2
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
        br 0 (;@2;)
      end
    end
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p1
          i64.const 255
          i64.and
          i64.const 76
          i64.ne
          br_if 0 (;@3;)
          local.get $p1
          i32.const 1048616
          i32.const 2
          local.get $l2
          i32.const 8
          i32.add
          i32.const 2
          call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17hce3ed893cada20d8E
          local.get $l2
          i64.load offset=8
          local.tee $p1
          i64.const 255
          i64.and
          i64.const 4
          i64.ne
          br_if 1 (;@2;)
          local.get $l2
          i32.const 24
          i32.add
          local.get $l2
          i64.load offset=16
          call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
          block  ;; label = @4
            local.get $l2
            i64.load offset=24
            i64.eqz
            i32.eqz
            br_if 0 (;@4;)
            local.get $l2
            i32.const 24
            i32.add
            i32.const 16
            i32.add
            i64.load
            local.set $l4
            local.get $p0
            local.get $l2
            i64.load offset=32
            i64.store offset=8
            local.get $p0
            local.get $p1
            i64.const 32
            i64.shr_u
            i32.wrap_i64
            i32.store offset=24
            local.get $p0
            i64.const 0
            i64.store
            local.get $p0
            i32.const 16
            i32.add
            local.get $l4
            i64.store
            br 3 (;@1;)
          end
          local.get $p0
          i64.const 1
          i64.store
          br 2 (;@1;)
        end
        local.get $p0
        i64.const 1
        i64.store
        br 1 (;@1;)
      end
      local.get $p0
      i64.const 1
      i64.store
    end
    local.get $l2
    i32.const 48
    i32.add
    global.set $__stack_pointer)
  (func $_ZN11soroban_sdk7storage8Instance3get17h6c2b08935b7df8acE (type $t9) (param $p0 i32)
    (local $l1 i64) (local $l2 i64)
    block  ;; label = @1
      block  ;; label = @2
        i32.const 1048656
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h963cbcfd3e9f50b8E
        local.tee $l1
        i64.const 2
        call $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE
        br_if 0 (;@2;)
        i64.const 0
        local.set $l2
        br 1 (;@1;)
      end
      i64.const 1
      local.set $l2
      local.get $l1
      i64.const 2
      call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E
      local.tee $l1
      i64.const 255
      i64.and
      i64.const 77
      i64.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0
    local.get $l1
    i64.store offset=8
    local.get $p0
    local.get $l2
    i64.store)
  (func $_ZN11soroban_sdk7storage9Temporary3get17h0a38f7fa46b99e53E (type $t5) (param $p0 i32) (param $p1 i32)
    (local $l2 i32) (local $l3 i64) (local $l4 i64) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    i64.const 0
    local.set $l3
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p1
          call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h963cbcfd3e9f50b8E
          local.tee $l4
          i64.const 0
          call $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE
          br_if 0 (;@3;)
          br 1 (;@2;)
        end
        local.get $l4
        i64.const 0
        call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E
        local.set $l3
        local.get $l2
        i64.const 2
        i64.store
        local.get $l3
        i64.const 255
        i64.and
        i64.const 76
        i64.ne
        br_if 1 (;@1;)
        local.get $l3
        i32.const 1048648
        i32.const 1
        local.get $l2
        i32.const 1
        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17hce3ed893cada20d8E
        local.get $l2
        i32.const 8
        i32.add
        local.get $l2
        i64.load
        call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
        local.get $l2
        i64.load offset=8
        i64.eqz
        i32.eqz
        br_if 1 (;@1;)
        local.get $l2
        i32.const 24
        i32.add
        i64.load
        local.set $l5
        local.get $l2
        i64.load offset=16
        local.set $l4
        i64.const 1
        local.set $l3
      end
      local.get $p0
      local.get $l4
      i64.store offset=8
      local.get $p0
      local.get $l3
      i64.store
      local.get $p0
      i32.const 16
      i32.add
      local.get $l5
      i64.store
      local.get $l2
      i32.const 32
      i32.add
      global.set $__stack_pointer
      return
    end
    unreachable
    unreachable)
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17hce3ed893cada20d8E (type $t10) (param $p0 i64) (param $p1 i32) (param $p2 i32) (param $p3 i32) (param $p4 i32)
    block  ;; label = @1
      local.get $p2
      local.get $p4
      i32.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0
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
    call $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h15a7786289874722E
    drop)
  (func $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE (type $t8) (param $p0 i32) (param $p1 i64)
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
  (func $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE (type $t11) (param $p0 i32) (param $p1 i32) (result i64)
    (local $l2 i64) (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32)
    block  ;; label = @1
      local.get $p1
      i32.const 9
      i32.gt_u
      br_if 0 (;@1;)
      i64.const 0
      local.set $l2
      local.get $p1
      local.set $l3
      local.get $p0
      local.set $l4
      block  ;; label = @2
        loop  ;; label = @3
          local.get $l3
          i32.eqz
          br_if 1 (;@2;)
          i32.const 1
          local.set $l5
          block  ;; label = @4
            local.get $l4
            i32.load8_u
            local.tee $l6
            i32.const 95
            i32.eq
            br_if 0 (;@4;)
            block  ;; label = @5
              local.get $l6
              i32.const -48
              i32.add
              i32.const 255
              i32.and
              i32.const 10
              i32.lt_u
              br_if 0 (;@5;)
              block  ;; label = @6
                local.get $l6
                i32.const -65
                i32.add
                i32.const 255
                i32.and
                i32.const 26
                i32.lt_u
                br_if 0 (;@6;)
                local.get $l6
                i32.const -97
                i32.add
                i32.const 255
                i32.and
                i32.const 25
                i32.gt_u
                br_if 5 (;@1;)
                local.get $l6
                i32.const -59
                i32.add
                local.set $l5
                br 2 (;@4;)
              end
              local.get $l6
              i32.const -53
              i32.add
              local.set $l5
              br 1 (;@4;)
            end
            local.get $l6
            i32.const -46
            i32.add
            local.set $l5
          end
          local.get $l2
          i64.const 6
          i64.shl
          local.get $l5
          i64.extend_i32_u
          i64.const 255
          i64.and
          i64.or
          local.set $l2
          local.get $l3
          i32.const -1
          i32.add
          local.set $l3
          local.get $l4
          i32.const 1
          i32.add
          local.set $l4
          br 0 (;@3;)
        end
      end
      local.get $l2
      i64.const 8
      i64.shl
      i64.const 14
      i64.or
      return
    end
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
    call $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h65f4c5e4b5b0b386E)
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf881b9c95e3d1d8eE (type $t11) (param $p0 i32) (param $p1 i32) (result i64)
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
  (func $_ZN26soroban_mint_lock_contract170_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_mint_lock_contract..MinterConfig$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17h23de3d6577b2396dE (type $t12) (param $p0 i64) (param $p1 i64) (param $p2 i32) (result i64)
    (local $l3 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $p0
    local.get $p1
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h36445e94b15e4b89E
    i64.store offset=8
    local.get $l3
    local.get $p2
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.store
    i32.const 1048616
    i32.const 2
    local.get $l3
    i32.const 2
    call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h6aaf488d9a7738b5E
    local.set $p1
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $p1)
  (func $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h36445e94b15e4b89E (type $t0) (param $p0 i64) (param $p1 i64) (result i64)
    block  ;; label = @1
      local.get $p0
      i64.const 36028797018963968
      i64.add
      i64.const 72057594037927935
      i64.gt_u
      br_if 0 (;@1;)
      local.get $p0
      local.get $p0
      i64.xor
      local.get $p0
      i64.const 63
      i64.shr_s
      local.get $p1
      i64.xor
      i64.or
      i64.const 0
      i64.ne
      br_if 0 (;@1;)
      local.get $p0
      i64.const 8
      i64.shl
      i64.const 11
      i64.or
      return
    end
    local.get $p1
    local.get $p0
    call $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17ha9df624d96cf2a1dE)
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h6aaf488d9a7738b5E (type $t13) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (result i64)
    block  ;; label = @1
      local.get $p1
      local.get $p3
      i32.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0
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
    local.get $p1
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    call $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17h999916ef23111b0dE)
  (func $_ZN26soroban_mint_lock_contract169_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_mint_lock_contract..MinterStats$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17h4711f591ca15e365E (type $t0) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    local.get $p0
    local.get $p1
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h36445e94b15e4b89E
    i64.store offset=8
    i32.const 1048648
    i32.const 1
    local.get $l2
    i32.const 8
    i32.add
    i32.const 1
    call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h6aaf488d9a7738b5E
    local.set $p1
    local.get $l2
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $p1)
  (func $set_admin (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 77
      i64.ne
      br_if 0 (;@1;)
      local.get $l1
      call $_ZN11soroban_sdk7storage8Instance3get17h6c2b08935b7df8acE
      block  ;; label = @2
        local.get $l1
        i64.load
        i32.wrap_i64
        i32.const 1
        i32.ne
        br_if 0 (;@2;)
        local.get $l1
        i64.load offset=8
        call $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE
        drop
      end
      i32.const 1048656
      call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h963cbcfd3e9f50b8E
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
    unreachable)
  (func $admin (type $t4) (result i64)
    call $_ZN26soroban_mint_lock_contract8Contract5admin17heaa28614828813f7E)
  (func $_ZN26soroban_mint_lock_contract8Contract5admin17heaa28614828813f7E (type $t4) (result i64)
    (local $l0 i32) (local $l1 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    call $_ZN11soroban_sdk7storage8Instance3get17h6c2b08935b7df8acE
    block  ;; label = @1
      local.get $l0
      i64.load
      i32.wrap_i64
      br_if 0 (;@1;)
      call $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E
      unreachable
    end
    local.get $l0
    i64.load offset=8
    local.set $l1
    local.get $l0
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l1)
  (func $set_minter (type $t2) (param $p0 i64) (param $p1 i64) (param $p2 i64) (result i64)
    (local $l3 i32) (local $l4 i64) (local $l5 i32)
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
      i64.const 77
      i64.ne
      br_if 0 (;@1;)
      local.get $l3
      local.get $p2
      call $_ZN160_$LT$soroban_mint_lock_contract..MinterConfig$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h4a0ff91a26aece47E
      local.get $l3
      i64.load
      i64.eqz
      i32.eqz
      br_if 0 (;@1;)
      local.get $l3
      i32.const 16
      i32.add
      i64.load
      local.set $p2
      local.get $l3
      i64.load offset=8
      local.set $l4
      local.get $l3
      i32.load offset=24
      local.set $l5
      call $_ZN26soroban_mint_lock_contract8Contract5admin17heaa28614828813f7E
      call $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE
      drop
      local.get $l3
      local.get $p1
      i64.store offset=16
      local.get $l3
      local.get $p0
      i64.store offset=8
      local.get $l3
      i32.const 1
      i32.store
      local.get $l3
      call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h963cbcfd3e9f50b8E
      local.get $l4
      local.get $p2
      local.get $l5
      call $_ZN26soroban_mint_lock_contract170_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_mint_lock_contract..MinterConfig$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17h23de3d6577b2396dE
      i64.const 1
      call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E
      drop
      local.get $l3
      i32.const 32
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    unreachable
    unreachable)
  (func $minter (type $t0) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32) (local $l3 i64) (local $l4 i64) (local $l5 i32) (local $l6 i32) (local $l7 i32)
    global.get $__stack_pointer
    i32.const 96
    i32.sub
    local.tee $l2
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
        local.get $l2
        local.get $p1
        i64.store offset=80
        local.get $l2
        local.get $p0
        i64.store offset=72
        local.get $l2
        i32.const 1
        i32.store offset=64
        local.get $l2
        i32.const 32
        i32.add
        local.get $l2
        i32.const 64
        i32.add
        call $_ZN11soroban_sdk7storage10Persistent3get17hd5af3c7d74ebed2cE
        block  ;; label = @3
          block  ;; label = @4
            local.get $l2
            i64.load offset=32
            i64.eqz
            br_if 0 (;@4;)
            local.get $l2
            i32.const 32
            i32.add
            i32.const 16
            i32.add
            i64.load
            local.set $l3
            local.get $l2
            i64.load offset=40
            local.set $l4
            local.get $l2
            i32.load offset=56
            local.set $l5
            call $_ZN11soroban_sdk6ledger6Ledger8sequence17hd263dedb0163c8deE
            local.set $l6
            local.get $l5
            i32.eqz
            br_if 3 (;@1;)
            local.get $l2
            local.get $p1
            i64.store offset=88
            local.get $l2
            local.get $p0
            i64.store offset=80
            local.get $l2
            local.get $l5
            i32.store offset=68
            local.get $l2
            i32.const 2
            i32.store offset=64
            local.get $l2
            local.get $l6
            local.get $l5
            i32.div_u
            local.tee $l7
            i32.store offset=72
            local.get $l2
            i32.const 8
            i32.add
            local.get $l2
            i32.const 64
            i32.add
            call $_ZN11soroban_sdk7storage9Temporary3get17h0a38f7fa46b99e53E
            local.get $l2
            i32.const 8
            i32.add
            i32.const 16
            i32.add
            i64.load
            local.set $p0
            local.get $l2
            i32.load offset=8
            local.set $l6
            local.get $l2
            i64.load offset=16
            local.set $p1
            local.get $l4
            local.get $l3
            local.get $l5
            call $_ZN26soroban_mint_lock_contract170_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_mint_lock_contract..MinterConfig$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17h23de3d6577b2396dE
            local.set $l3
            local.get $l2
            local.get $p1
            i64.const 0
            local.get $l6
            select
            local.get $p0
            i64.const 0
            local.get $l6
            select
            call $_ZN26soroban_mint_lock_contract169_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_mint_lock_contract..MinterStats$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17h4711f591ca15e365E
            i64.store offset=80
            local.get $l2
            local.get $l7
            i64.extend_i32_u
            i64.const 32
            i64.shl
            i64.const 4
            i64.or
            i64.store offset=72
            local.get $l2
            local.get $l3
            i64.store offset=64
            local.get $l2
            i32.const 64
            i32.add
            i32.const 3
            call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf881b9c95e3d1d8eE
            local.set $p0
            br 1 (;@3;)
          end
          i64.const 4294967299
          local.set $p0
        end
        local.get $l2
        i32.const 96
        i32.add
        global.set $__stack_pointer
        local.get $p0
        return
      end
      unreachable
      unreachable
    end
    call $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E
    unreachable)
  (func $_ZN11soroban_sdk6ledger6Ledger8sequence17hd263dedb0163c8deE (type $t14) (result i32)
    call $_ZN17soroban_env_guest5guest7context19get_ledger_sequence17h997670b190a8871eE
    i64.const 32
    i64.shr_u
    i32.wrap_i64)
  (func $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E (type $t15)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $mint (type $t3) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (result i64)
    (local $l4 i32) (local $l5 i64) (local $l6 i32) (local $l7 i64) (local $l8 i64) (local $l9 i32) (local $l10 i32) (local $l11 i64) (local $l12 i64)
    global.get $__stack_pointer
    i32.const 96
    i32.sub
    local.tee $l4
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              local.get $p0
              i64.const 255
              i64.and
              i64.const 77
              i64.ne
              br_if 0 (;@5;)
              local.get $p1
              i64.const 255
              i64.and
              i64.const 77
              i64.ne
              br_if 0 (;@5;)
              local.get $p2
              i64.const 255
              i64.and
              i64.const 77
              i64.ne
              br_if 0 (;@5;)
              local.get $l4
              i32.const 64
              i32.add
              local.get $p3
              call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
              local.get $l4
              i64.load offset=64
              i64.eqz
              i32.eqz
              br_if 0 (;@5;)
              local.get $l4
              local.get $l4
              i64.load offset=72
              local.tee $l5
              local.get $l4
              i32.const 80
              i32.add
              i64.load
              local.tee $p3
              call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h36445e94b15e4b89E
              i64.store offset=48
              local.get $l4
              local.get $p2
              i64.store offset=40
              local.get $l4
              local.get $p0
              i64.store offset=32
              i32.const 0
              local.set $l6
              loop  ;; label = @6
                block  ;; label = @7
                  local.get $l6
                  i32.const 24
                  i32.ne
                  br_if 0 (;@7;)
                  i32.const 0
                  local.set $l6
                  block  ;; label = @8
                    loop  ;; label = @9
                      local.get $l6
                      i32.const 24
                      i32.eq
                      br_if 1 (;@8;)
                      local.get $l4
                      i32.const 64
                      i32.add
                      local.get $l6
                      i32.add
                      local.get $l4
                      i32.const 32
                      i32.add
                      local.get $l6
                      i32.add
                      i64.load
                      i64.store
                      local.get $l6
                      i32.const 8
                      i32.add
                      local.set $l6
                      br 0 (;@9;)
                    end
                  end
                  local.get $p1
                  local.get $l4
                  i32.const 64
                  i32.add
                  i32.const 3
                  call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf881b9c95e3d1d8eE
                  call $_ZN17soroban_env_guest5guest7address21require_auth_for_args17h6ce4b5b084351056E
                  drop
                  block  ;; label = @8
                    local.get $p3
                    i64.const 0
                    i64.ge_s
                    br_if 0 (;@8;)
                    i64.const 12884901891
                    local.set $p1
                    br 7 (;@1;)
                  end
                  block  ;; label = @8
                    call $_ZN26soroban_mint_lock_contract8Contract5admin17heaa28614828813f7E
                    local.get $p1
                    call $_ZN17soroban_env_guest5guest7context7obj_cmp17h189bc77d88b5cf98E
                    i64.eqz
                    br_if 0 (;@8;)
                    local.get $l4
                    local.get $p1
                    i64.store offset=80
                    local.get $l4
                    local.get $p0
                    i64.store offset=72
                    local.get $l4
                    i32.const 1
                    i32.store offset=64
                    local.get $l4
                    i32.const 32
                    i32.add
                    local.get $l4
                    i32.const 64
                    i32.add
                    call $_ZN11soroban_sdk7storage10Persistent3get17hd5af3c7d74ebed2cE
                    local.get $l4
                    i64.load offset=32
                    i64.eqz
                    br_if 6 (;@2;)
                    local.get $l4
                    i32.const 32
                    i32.add
                    i32.const 16
                    i32.add
                    i64.load
                    local.set $l7
                    local.get $l4
                    i64.load offset=40
                    local.set $l8
                    local.get $l4
                    i32.load offset=56
                    local.set $l6
                    call $_ZN11soroban_sdk6ledger6Ledger8sequence17hd263dedb0163c8deE
                    local.set $l9
                    local.get $l6
                    i32.eqz
                    br_if 4 (;@4;)
                    local.get $l4
                    local.get $p1
                    i64.store offset=88
                    local.get $l4
                    local.get $p0
                    i64.store offset=80
                    local.get $l4
                    i32.const 2
                    i32.store offset=64
                    local.get $l4
                    local.get $l6
                    i32.store offset=68
                    local.get $l4
                    local.get $l9
                    local.get $l6
                    i32.div_u
                    local.tee $l10
                    i32.store offset=72
                    local.get $l4
                    i32.const 8
                    i32.add
                    local.get $l4
                    i32.const 64
                    i32.add
                    call $_ZN11soroban_sdk7storage9Temporary3get17h0a38f7fa46b99e53E
                    local.get $l4
                    i32.const 8
                    i32.add
                    i32.const 16
                    i32.add
                    i64.load
                    i64.const 0
                    local.get $l4
                    i32.load offset=8
                    local.tee $l9
                    select
                    local.tee $l11
                    local.get $p3
                    i64.xor
                    i64.const -1
                    i64.xor
                    local.get $l11
                    local.get $l11
                    local.get $p3
                    i64.add
                    local.get $l4
                    i64.load offset=16
                    i64.const 0
                    local.get $l9
                    select
                    local.tee $p1
                    local.get $l5
                    i64.add
                    local.tee $l12
                    local.get $p1
                    i64.lt_u
                    i64.extend_i32_u
                    i64.add
                    local.tee $p1
                    i64.xor
                    i64.and
                    i64.const 0
                    i64.lt_s
                    br_if 4 (;@4;)
                    local.get $l12
                    local.get $l8
                    i64.gt_u
                    local.get $p1
                    local.get $l7
                    i64.gt_s
                    local.get $p1
                    local.get $l7
                    i64.eq
                    select
                    br_if 5 (;@3;)
                    local.get $l4
                    i32.const 64
                    i32.add
                    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h963cbcfd3e9f50b8E
                    local.get $l12
                    local.get $p1
                    call $_ZN26soroban_mint_lock_contract169_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_mint_lock_contract..MinterStats$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17h4711f591ca15e365E
                    i64.const 0
                    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E
                    drop
                    local.get $l10
                    i64.extend_i32_u
                    local.get $l6
                    i64.extend_i32_u
                    i64.mul
                    local.tee $p1
                    i64.const 32
                    i64.shr_u
                    i32.wrap_i64
                    br_if 4 (;@4;)
                    local.get $l4
                    i32.const 64
                    i32.add
                    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h963cbcfd3e9f50b8E
                    i64.const 0
                    i64.const 4
                    local.get $p1
                    i32.wrap_i64
                    i64.extend_i32_u
                    i64.const 32
                    i64.shl
                    i64.const 4
                    i64.or
                    call $_ZN17soroban_env_guest5guest6ledger24extend_contract_data_ttl17hfe78b0ca805be00cE
                    drop
                  end
                  local.get $l4
                  local.get $l5
                  local.get $p3
                  call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h36445e94b15e4b89E
                  i64.store offset=40
                  local.get $l4
                  local.get $p2
                  i64.store offset=32
                  i32.const 0
                  local.set $l6
                  block  ;; label = @8
                    loop  ;; label = @9
                      block  ;; label = @10
                        local.get $l6
                        i32.const 16
                        i32.ne
                        br_if 0 (;@10;)
                        i32.const 0
                        local.set $l6
                        block  ;; label = @11
                          loop  ;; label = @12
                            local.get $l6
                            i32.const 16
                            i32.eq
                            br_if 1 (;@11;)
                            local.get $l4
                            i32.const 64
                            i32.add
                            local.get $l6
                            i32.add
                            local.get $l4
                            i32.const 32
                            i32.add
                            local.get $l6
                            i32.add
                            i64.load
                            i64.store
                            local.get $l6
                            i32.const 8
                            i32.add
                            local.set $l6
                            br 0 (;@12;)
                          end
                        end
                        i64.const 2
                        local.set $p1
                        local.get $p0
                        i64.const 3404527886
                        local.get $l4
                        i32.const 64
                        i32.add
                        i32.const 2
                        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf881b9c95e3d1d8eE
                        call $_ZN17soroban_env_guest5guest4call4call17he38ff75d18335ef7E
                        i64.const 255
                        i64.and
                        i64.const 2
                        i64.ne
                        br_if 2 (;@8;)
                        br 9 (;@1;)
                      end
                      local.get $l4
                      i32.const 64
                      i32.add
                      local.get $l6
                      i32.add
                      i64.const 2
                      i64.store
                      local.get $l6
                      i32.const 8
                      i32.add
                      local.set $l6
                      br 0 (;@9;)
                    end
                  end
                  local.get $l4
                  i32.const 64
                  i32.add
                  call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
                  unreachable
                end
                local.get $l4
                i32.const 64
                i32.add
                local.get $l6
                i32.add
                i64.const 2
                i64.store
                local.get $l6
                i32.const 8
                i32.add
                local.set $l6
                br 0 (;@6;)
              end
            end
            unreachable
            unreachable
          end
          call $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E
          unreachable
        end
        i64.const 8589934595
        local.set $p1
        br 1 (;@1;)
      end
      i64.const 4294967299
      local.set $p1
    end
    local.get $l4
    i32.const 96
    i32.add
    global.set $__stack_pointer
    local.get $p1)
  (func $_ZN4core6result13unwrap_failed17h472431483d5eea7fE (type $t9) (param $p0 i32)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E (type $t15)
    call $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E
    unreachable)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t15)
    unreachable
    unreachable)
  (func $_ (type $t15))
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048688))
  (global $__heap_base i32 (i32.const 1048688))
  (export "memory" (memory $memory))
  (export "set_admin" (func $set_admin))
  (export "admin" (func $admin))
  (export "set_minter" (func $set_minter))
  (export "minter" (func $minter))
  (export "mint" (func $mint))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (data $.rodata (i32.const 1048576) "AdminMinterMinterStatsepoch_lengthlimit\00\16\00\10\00\0c\00\00\00\22\00\10\00\05\00\00\00consumed_limit\00\008\00\10\00\0e\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"))
