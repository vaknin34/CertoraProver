(module $reflector_subscriptions.wasm
  (type $t0 (func (param i32 i32 i32) (result i32)))
  (type $t1 (func (param i32 i32) (result i32)))
  (type $t2 (func (param i64) (result i64)))
  (type $t3 (func (param i64 i64) (result i64)))
  (type $t4 (func (param i64 i64 i64) (result i64)))
  (type $t5 (func (param i64 i64 i64 i64) (result i64)))
  (type $t6 (func (result i64)))
  (type $t7 (func (param i32)))
  (type $t8 (func (param i32 i64)))
  (type $t9 (func (param i32 i32 i32)))
  (type $t10 (func (param i32 i32) (result i64)))
  (type $t11 (func (param i64 i64) (result i32)))
  (type $t12 (func (param i32 i32 i64)))
  (type $t13 (func (param i32) (result i64)))
  (type $t14 (func (param i64 i32 i32 i32 i32)))
  (type $t15 (func (param i32 i32 i32 i32) (result i64)))
  (type $t16 (func (param i64 i64 i64)))
  (type $t17 (func (param i64)))
  (type $t18 (func))
  (type $t19 (func (param i64 i64 i64 i64)))
  (type $t20 (func (result i32)))
  (type $t21 (func (param i64 i32)))
  (type $t22 (func (param i32 i64 i64)))
  (type $t23 (func (param i64 i64 i64 i32) (result i64)))
  (type $t24 (func (param i64 i32) (result i64)))
  (type $t25 (func (param i64 i64)))
  (type $t26 (func (param i32 i32)))
  (type $t27 (func (param i64 i32 i32) (result i32)))
  (type $t28 (func (param i32 i32 i32 i32 i32 i32) (result i32)))
  (type $t29 (func (param i32 i32 i32 i32 i32) (result i32)))
  (type $t30 (func (param i32 i64 i64 i32)))
  (type $t31 (func (param i32 i64 i64 i64 i64)))
  (import "i" "_" (func $_ZN17soroban_env_guest5guest3int12obj_from_u6417h7041e9e9cf62b21dE (type $t2)))
  (import "i" "0" (func $_ZN17soroban_env_guest5guest3int10obj_to_u6417h04c12c1e1e50ea61E (type $t2)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17hcea43a344896b5dcE (type $t3)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17haa25b294db7ef9deE (type $t4)))
  (import "b" "i" (func $_ZN17soroban_env_guest5guest3buf29string_new_from_linear_memory17ha41c1e98589f1074E (type $t3)))
  (import "i" "6" (func $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17h6344a1a3ec42d4d4E (type $t3)))
  (import "d" "_" (func $_ZN17soroban_env_guest5guest4call4call17hda79ed52b11bcd56E (type $t4)))
  (import "l" "7" (func $_ZN17soroban_env_guest5guest6ledger24extend_contract_data_ttl17h8fab322f10152870E (type $t5)))
  (import "a" "0" (func $_ZN17soroban_env_guest5guest7address12require_auth17heac8c347e0e63eefE (type $t2)))
  (import "x" "0" (func $_ZN17soroban_env_guest5guest7context7obj_cmp17hb0d21973d6fefaacE (type $t3)))
  (import "x" "7" (func $_ZN17soroban_env_guest5guest7context28get_current_contract_address17hcc67655a7974e4f6E (type $t6)))
  (import "x" "4" (func $_ZN17soroban_env_guest5guest7context20get_ledger_timestamp17h1842398ca4defda9E (type $t6)))
  (import "x" "3" (func $_ZN17soroban_env_guest5guest7context19get_ledger_sequence17hc627523f88a30ab8E (type $t6)))
  (import "x" "8" (func $_ZN17soroban_env_guest5guest7context25get_max_live_until_ledger17h77a0bfec84a4f373E (type $t6)))
  (import "x" "1" (func $_ZN17soroban_env_guest5guest7context14contract_event17ha9a5af34bd21bbfcE (type $t3)))
  (import "l" "6" (func $_ZN17soroban_env_guest5guest6ledger28update_current_contract_wasm17hf31ebfa6a5376f4eE (type $t2)))
  (import "b" "8" (func $_ZN17soroban_env_guest5guest3buf9bytes_len17h5f2677f709d7063cE (type $t2)))
  (import "l" "2" (func $_ZN17soroban_env_guest5guest6ledger17del_contract_data17hef3bcb945e85743fE (type $t3)))
  (import "env" "CVT_assert_c" (func $CVT_assert_c (type $t7)))
  (import "env" "CVT_nondet_u64_c" (func $CVT_nondet_u64_c (type $t6)))
  (import "m" "9" (func $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17haa91059c63dd8dc5E (type $t4)))
  (import "m" "a" (func $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h5316e210cd652bdcE (type $t5)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17hb096a2627ae77ae2E (type $t3)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17h97b5fbbaa6745c52E (type $t3)))
  (import "x" "5" (func $_ZN17soroban_env_guest5guest7context15fail_with_error17hada9d6da67b2f63eE (type $t2)))
  (func $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E (type $t2) (param $p0 i64) (result i64)
    block  ;; label = @1
      local.get $p0
      i64.const 72057594037927935
      i64.gt_u
      br_if 0 (;@1;)
      local.get $p0
      i64.const 8
      i64.shl
      i64.const 6
      i64.or
      return
    end
    local.get $p0
    call $_ZN17soroban_env_guest5guest3int12obj_from_u6417h7041e9e9cf62b21dE)
  (func $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E (type $t8) (param $p0 i32) (param $p1 i64)
    (local $l2 i32) (local $l3 i64)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p1
        i32.wrap_i64
        i32.const 255
        i32.and
        local.tee $l2
        i32.const 64
        i32.eq
        br_if 0 (;@2;)
        block  ;; label = @3
          local.get $l2
          i32.const 6
          i32.eq
          br_if 0 (;@3;)
          i64.const 1
          local.set $l3
          i64.const 34359740419
          local.set $p1
          br 2 (;@1;)
        end
        local.get $p1
        i64.const 8
        i64.shr_u
        local.set $p1
        i64.const 0
        local.set $l3
        br 1 (;@1;)
      end
      i64.const 0
      local.set $l3
      local.get $p1
      call $_ZN17soroban_env_guest5guest3int10obj_to_u6417h04c12c1e1e50ea61E
      local.set $p1
    end
    local.get $p0
    local.get $p1
    i64.store offset=8
    local.get $p0
    local.get $l3
    i64.store)
  (func $_ZN11soroban_sdk7storage8Instance3get17h4e6184aa5b3b788eE (type $t9) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p1
          local.get $p2
          call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hba9cab496d62071bE
          local.tee $l4
          i64.const 2
          call $_ZN11soroban_sdk7storage7Storage12has_internal17h0e397f3e6f3f4c21E
          br_if 0 (;@3;)
          i64.const 0
          local.set $l4
          br 1 (;@2;)
        end
        local.get $l3
        local.get $l4
        i64.const 2
        call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17hcea43a344896b5dcE
        call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E
        local.get $l3
        i64.load
        i32.wrap_i64
        br_if 1 (;@1;)
        local.get $l3
        i64.load offset=8
        local.set $l5
        i64.const 1
        local.set $l4
      end
      local.get $p0
      local.get $l5
      i64.store offset=8
      local.get $p0
      local.get $l4
      i64.store
      local.get $l3
      i32.const 16
      i32.add
      global.set $__stack_pointer
      return
    end
    unreachable
    unreachable)
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hba9cab496d62071bE (type $t10) (param $p0 i32) (param $p1 i32) (result i64)
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
    call $_ZN17soroban_env_guest5guest3buf29string_new_from_linear_memory17ha41c1e98589f1074E)
  (func $_ZN11soroban_sdk7storage7Storage12has_internal17h0e397f3e6f3f4c21E (type $t11) (param $p0 i64) (param $p1 i64) (result i32)
    local.get $p0
    local.get $p1
    call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17h97b5fbbaa6745c52E
    i64.const 1
    i64.eq)
  (func $_ZN11soroban_sdk7storage8Instance3get17h52ab23d73fb8ab6bE (type $t9) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i64) (local $l4 i64)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p1
        local.get $p2
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hba9cab496d62071bE
        local.tee $l3
        i64.const 2
        call $_ZN11soroban_sdk7storage7Storage12has_internal17h0e397f3e6f3f4c21E
        br_if 0 (;@2;)
        i64.const 0
        local.set $l4
        br 1 (;@1;)
      end
      i64.const 1
      local.set $l4
      local.get $l3
      i64.const 2
      call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17hcea43a344896b5dcE
      local.tee $l3
      i64.const 255
      i64.and
      i64.const 77
      i64.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0
    local.get $l3
    i64.store offset=8
    local.get $p0
    local.get $l4
    i64.store)
  (func $_ZN11soroban_sdk7storage8Instance3set17h6dc43fc876a1ad1aE (type $t12) (param $p0 i32) (param $p1 i32) (param $p2 i64)
    local.get $p0
    local.get $p1
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hba9cab496d62071bE
    local.get $p2
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17haa25b294db7ef9deE
    drop)
  (func $_ZN11soroban_sdk7storage8Instance3set17hf896aec157f951feE (type $t12) (param $p0 i32) (param $p1 i32) (param $p2 i64)
    local.get $p0
    local.get $p1
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hba9cab496d62071bE
    local.get $p2
    call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17haa25b294db7ef9deE
    drop)
  (func $_ZN42_$LT$$RF$T$u20$as$u20$core..fmt..Debug$GT$3fmt17h8e5c037cbbf6591fE (type $t0) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    local.get $p1
    local.get $p0
    i32.load8_u
    i32.const 2
    i32.shl
    local.tee $p0
    i32.const 1048940
    i32.add
    i32.load
    local.get $p0
    i32.const 1048920
    i32.add
    i32.load
    local.get $p2
    i32.load offset=12
    call_indirect $T0 (type $t0))
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h73fad27a55c2a023E (type $t13) (param $p0 i32) (result i64)
    (local $l1 i32) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    local.get $p0
    i64.load offset=16
    i64.store offset=16
    local.get $l1
    local.get $p0
    i64.load offset=8
    i64.store offset=8
    local.get $l1
    local.get $p0
    i64.load
    i64.store
    i32.const 0
    local.set $p0
    loop (result i64)  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i32.const 24
        i32.ne
        br_if 0 (;@2;)
        i32.const 0
        local.set $p0
        block  ;; label = @3
          loop  ;; label = @4
            local.get $p0
            i32.const 24
            i32.eq
            br_if 1 (;@3;)
            local.get $l1
            i32.const 24
            i32.add
            local.get $p0
            i32.add
            local.get $l1
            local.get $p0
            i32.add
            i64.load
            i64.store
            local.get $p0
            i32.const 8
            i32.add
            local.set $p0
            br 0 (;@4;)
          end
        end
        local.get $l1
        i32.const 24
        i32.add
        i32.const 3
        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17h79c443bd00384008E
        local.set $l2
        local.get $l1
        i32.const 48
        i32.add
        global.set $__stack_pointer
        local.get $l2
        return
      end
      local.get $l1
      i32.const 24
      i32.add
      local.get $p0
      i32.add
      i64.const 2
      i64.store
      local.get $p0
      i32.const 8
      i32.add
      local.set $p0
      br 0 (;@1;)
    end)
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17h79c443bd00384008E (type $t10) (param $p0 i32) (param $p1 i32) (result i64)
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
    call $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17hb096a2627ae77ae2E)
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17he412710998833677E (type $t13) (param $p0 i32) (result i64)
    (local $l1 i32) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $p0
    i64.load
    call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E
    local.set $l2
    local.get $l1
    local.get $p0
    i32.const 8
    i32.add
    call $_ZN23reflector_subscriptions5types12subscription188_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$reflector_subscriptions..types..subscription..Subscription$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17hb05340ab0a18289cE
    i64.store offset=8
    local.get $l1
    local.get $l2
    i64.store
    local.get $l1
    i32.const 2
    call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17h79c443bd00384008E
    local.set $l2
    local.get $l1
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l2)
  (func $_ZN23reflector_subscriptions5types12subscription188_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$reflector_subscriptions..types..subscription..Subscription$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17hb05340ab0a18289cE (type $t13) (param $p0 i32) (result i64)
    (local $l1 i32) (local $l2 i64) (local $l3 i64) (local $l4 i64) (local $l5 i64) (local $l6 i64) (local $l7 i64) (local $l8 i32)
    global.get $__stack_pointer
    i32.const 80
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $p0
    i64.load offset=48
    call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E
    local.set $l2
    local.get $p0
    i64.load offset=8
    local.get $p0
    i64.load offset=16
    call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h6acffcb7de657ea7E
    local.set $l3
    local.get $p0
    i64.load32_u offset=68
    local.set $l4
    local.get $p0
    i64.load
    local.set $l5
    local.get $p0
    i64.load offset=24
    local.get $p0
    i64.load offset=32
    call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h6acffcb7de657ea7E
    local.set $l6
    local.get $p0
    i64.load32_u offset=64
    local.set $l7
    local.get $p0
    i32.load8_u offset=72
    local.set $l8
    local.get $l1
    local.get $p0
    i64.load offset=56
    call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E
    i64.store offset=64
    local.get $l1
    i64.const 4294967300
    i64.const 4
    local.get $l8
    select
    i64.store offset=48
    local.get $l1
    local.get $l6
    i64.store offset=40
    local.get $l1
    local.get $l5
    i64.store offset=32
    local.get $l1
    local.get $l4
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.store offset=24
    local.get $l1
    local.get $l3
    i64.store offset=16
    local.get $l1
    local.get $l2
    i64.store offset=8
    local.get $l1
    local.get $p0
    i64.load offset=40
    i64.store offset=72
    local.get $l1
    local.get $l7
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.store offset=56
    i32.const 1048764
    i32.const 9
    local.get $l1
    i32.const 8
    i32.add
    i32.const 9
    call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17he93fd61ef59aa425E
    local.set $l2
    local.get $l1
    i32.const 80
    i32.add
    global.set $__stack_pointer
    local.get $l2)
  (func $_ZN68_$LT$core..num..error..ParseIntError$u20$as$u20$core..fmt..Debug$GT$3fmt17h8f58b2f81c940f7dE (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32) (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    i32.const 1
    local.set $l3
    block  ;; label = @1
      local.get $p1
      i32.load offset=20
      local.tee $l4
      i32.const 1048635
      i32.const 13
      local.get $p1
      i32.load offset=24
      local.tee $l5
      i32.load offset=12
      local.tee $l6
      call_indirect $T0 (type $t0)
      br_if 0 (;@1;)
      block  ;; label = @2
        local.get $p1
        i32.load8_u offset=28
        i32.const 4
        i32.and
        br_if 0 (;@2;)
        local.get $l4
        i32.const 1049036
        i32.const 3
        local.get $l6
        call_indirect $T0 (type $t0)
        br_if 1 (;@1;)
        local.get $l4
        i32.const 1048648
        i32.const 4
        local.get $l6
        call_indirect $T0 (type $t0)
        br_if 1 (;@1;)
        local.get $l4
        i32.const 1049003
        i32.const 2
        local.get $l6
        call_indirect $T0 (type $t0)
        br_if 1 (;@1;)
        local.get $p0
        local.get $l4
        local.get $l5
        call $_ZN42_$LT$$RF$T$u20$as$u20$core..fmt..Debug$GT$3fmt17h8e5c037cbbf6591fE
        br_if 1 (;@1;)
        local.get $l4
        i32.const 1049045
        i32.const 2
        local.get $l6
        call_indirect $T0 (type $t0)
        local.set $l3
        br 1 (;@1;)
      end
      local.get $l4
      i32.const 1049039
      i32.const 3
      local.get $l6
      call_indirect $T0 (type $t0)
      br_if 0 (;@1;)
      local.get $l2
      local.get $l5
      i32.store offset=4
      local.get $l2
      local.get $l4
      i32.store
      i32.const 1
      local.set $l3
      local.get $l2
      i32.const 1
      i32.store8 offset=15
      local.get $l2
      local.get $l2
      i32.const 15
      i32.add
      i32.store offset=8
      local.get $l2
      i32.const 1048648
      i32.const 4
      call $_ZN68_$LT$core..fmt..builders..PadAdapter$u20$as$u20$core..fmt..Write$GT$9write_str17hf46b591acfd1be0dE
      br_if 0 (;@1;)
      local.get $l2
      i32.const 1049003
      i32.const 2
      call $_ZN68_$LT$core..fmt..builders..PadAdapter$u20$as$u20$core..fmt..Write$GT$9write_str17hf46b591acfd1be0dE
      br_if 0 (;@1;)
      local.get $p0
      local.get $l2
      i32.const 1049008
      call $_ZN42_$LT$$RF$T$u20$as$u20$core..fmt..Debug$GT$3fmt17h8e5c037cbbf6591fE
      br_if 0 (;@1;)
      i32.const 1
      local.set $l3
      local.get $l2
      i32.const 1049042
      i32.const 2
      call $_ZN68_$LT$core..fmt..builders..PadAdapter$u20$as$u20$core..fmt..Write$GT$9write_str17hf46b591acfd1be0dE
      br_if 0 (;@1;)
      local.get $l4
      i32.const 1049044
      i32.const 1
      local.get $l6
      call_indirect $T0 (type $t0)
      local.set $l3
    end
    local.get $l2
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l3)
  (func $_ZN68_$LT$core..fmt..builders..PadAdapter$u20$as$u20$core..fmt..Write$GT$9write_str17hf46b591acfd1be0dE (type $t0) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32) (local $l7 i32) (local $l8 i32) (local $l9 i32) (local $l10 i32) (local $l11 i32) (local $l12 i32) (local $l13 i32)
    local.get $p1
    i32.const -1
    i32.add
    local.set $l3
    local.get $p0
    i32.load offset=4
    local.set $l4
    local.get $p0
    i32.load
    local.set $l5
    local.get $p0
    i32.load offset=8
    local.set $l6
    i32.const 0
    local.set $l7
    i32.const 0
    local.set $l8
    loop  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $l7
          local.get $p2
          i32.gt_u
          br_if 0 (;@3;)
          loop  ;; label = @4
            local.get $p1
            local.get $l7
            i32.add
            local.set $l9
            block  ;; label = @5
              block  ;; label = @6
                block  ;; label = @7
                  block  ;; label = @8
                    local.get $p2
                    local.get $l7
                    i32.sub
                    local.tee $l10
                    i32.const 7
                    i32.gt_u
                    br_if 0 (;@8;)
                    local.get $p2
                    local.get $l7
                    i32.ne
                    br_if 1 (;@7;)
                    local.get $p2
                    local.set $l7
                    br 5 (;@3;)
                  end
                  block  ;; label = @8
                    block  ;; label = @9
                      local.get $l9
                      i32.const 3
                      i32.add
                      i32.const -4
                      i32.and
                      local.tee $l11
                      local.get $l9
                      i32.sub
                      local.tee $l12
                      i32.eqz
                      br_if 0 (;@9;)
                      i32.const 0
                      local.set $p0
                      loop  ;; label = @10
                        local.get $l9
                        local.get $p0
                        i32.add
                        i32.load8_u
                        i32.const 10
                        i32.eq
                        br_if 5 (;@5;)
                        local.get $l12
                        local.get $p0
                        i32.const 1
                        i32.add
                        local.tee $p0
                        i32.ne
                        br_if 0 (;@10;)
                      end
                      local.get $l12
                      local.get $l10
                      i32.const -8
                      i32.add
                      local.tee $l13
                      i32.le_u
                      br_if 1 (;@8;)
                      br 3 (;@6;)
                    end
                    local.get $l10
                    i32.const -8
                    i32.add
                    local.set $l13
                  end
                  loop  ;; label = @8
                    local.get $l11
                    i32.const 4
                    i32.add
                    i32.load
                    local.tee $p0
                    i32.const 168430090
                    i32.xor
                    i32.const -16843009
                    i32.add
                    local.get $p0
                    i32.const -1
                    i32.xor
                    i32.and
                    local.get $l11
                    i32.load
                    local.tee $p0
                    i32.const 168430090
                    i32.xor
                    i32.const -16843009
                    i32.add
                    local.get $p0
                    i32.const -1
                    i32.xor
                    i32.and
                    i32.or
                    i32.const -2139062144
                    i32.and
                    br_if 2 (;@6;)
                    local.get $l11
                    i32.const 8
                    i32.add
                    local.set $l11
                    local.get $l12
                    i32.const 8
                    i32.add
                    local.tee $l12
                    local.get $l13
                    i32.le_u
                    br_if 0 (;@8;)
                    br 2 (;@6;)
                  end
                end
                i32.const 0
                local.set $p0
                loop  ;; label = @7
                  local.get $l9
                  local.get $p0
                  i32.add
                  i32.load8_u
                  i32.const 10
                  i32.eq
                  br_if 2 (;@5;)
                  local.get $l10
                  local.get $p0
                  i32.const 1
                  i32.add
                  local.tee $p0
                  i32.ne
                  br_if 0 (;@7;)
                end
                local.get $p2
                local.set $l7
                br 3 (;@3;)
              end
              block  ;; label = @6
                local.get $l12
                local.get $l10
                i32.ne
                br_if 0 (;@6;)
                local.get $p2
                local.set $l7
                br 3 (;@3;)
              end
              local.get $l9
              local.get $l12
              i32.add
              local.set $l11
              local.get $p2
              local.get $l12
              i32.sub
              local.get $l7
              i32.sub
              local.set $l10
              i32.const 0
              local.set $p0
              block  ;; label = @6
                loop  ;; label = @7
                  local.get $l11
                  local.get $p0
                  i32.add
                  i32.load8_u
                  i32.const 10
                  i32.eq
                  br_if 1 (;@6;)
                  local.get $l10
                  local.get $p0
                  i32.const 1
                  i32.add
                  local.tee $p0
                  i32.ne
                  br_if 0 (;@7;)
                end
                local.get $p2
                local.set $l7
                br 3 (;@3;)
              end
              local.get $p0
              local.get $l12
              i32.add
              local.set $p0
            end
            local.get $p0
            local.get $l7
            i32.add
            local.tee $l11
            i32.const 1
            i32.add
            local.set $l7
            block  ;; label = @5
              local.get $l11
              local.get $p2
              i32.ge_u
              br_if 0 (;@5;)
              local.get $l9
              local.get $p0
              i32.add
              i32.load8_u
              i32.const 10
              i32.ne
              br_if 0 (;@5;)
              i32.const 0
              local.set $l9
              local.get $l7
              local.set $l12
              local.get $l7
              local.set $p0
              br 3 (;@2;)
            end
            local.get $l7
            local.get $p2
            i32.le_u
            br_if 0 (;@4;)
          end
        end
        i32.const 1
        local.set $l9
        local.get $l8
        local.set $l12
        local.get $p2
        local.set $p0
        local.get $l8
        local.get $p2
        i32.ne
        br_if 0 (;@2;)
        i32.const 0
        return
      end
      block  ;; label = @2
        local.get $l6
        i32.load8_u
        i32.eqz
        br_if 0 (;@2;)
        local.get $l5
        i32.const 1049032
        i32.const 4
        local.get $l4
        i32.load offset=12
        call_indirect $T0 (type $t0)
        i32.eqz
        br_if 0 (;@2;)
        i32.const 1
        return
      end
      local.get $p0
      local.get $l8
      i32.sub
      local.set $l10
      i32.const 0
      local.set $l11
      block  ;; label = @2
        local.get $p0
        local.get $l8
        i32.eq
        br_if 0 (;@2;)
        local.get $l3
        local.get $p0
        i32.add
        i32.load8_u
        i32.const 10
        i32.eq
        local.set $l11
      end
      local.get $p1
      local.get $l8
      i32.add
      local.set $p0
      local.get $l6
      local.get $l11
      i32.store8
      local.get $l12
      local.set $l8
      local.get $l5
      local.get $p0
      local.get $l10
      local.get $l4
      i32.load offset=12
      call_indirect $T0 (type $t0)
      local.tee $p0
      local.get $l9
      i32.or
      i32.eqz
      br_if 0 (;@1;)
    end
    local.get $p0)
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h31b0e2b4650a4451E (type $t8) (param $p0 i32) (param $p1 i64)
    (local $l2 i32) (local $l3 i32) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 16
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
          i32.const 1048688
          i32.const 2
          local.get $l2
          i32.const 2
          call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h808038e83f4d1800E
          local.get $l2
          i64.load
          local.tee $p1
          i64.const 255
          i64.and
          i64.const 73
          i64.ne
          br_if 1 (;@2;)
          block  ;; label = @4
            local.get $l2
            i64.load offset=8
            local.tee $l4
            i64.const 255
            i64.and
            i64.const 73
            i64.ne
            br_if 0 (;@4;)
            local.get $p0
            local.get $l4
            i64.store offset=16
            local.get $p0
            local.get $p1
            i64.store offset=8
            local.get $p0
            i64.const 0
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
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h808038e83f4d1800E (type $t14) (param $p0 i64) (param $p1 i32) (param $p2 i32) (param $p3 i32) (param $p4 i32)
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
    call $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h5316e210cd652bdcE
    drop)
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h6acffcb7de657ea7E (type $t3) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    local.get $p1
    i64.store offset=8
    local.get $l2
    local.get $p0
    i64.store
    i32.const 1048688
    i32.const 2
    local.get $l2
    i32.const 2
    call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17he93fd61ef59aa425E
    local.set $p1
    local.get $l2
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $p1)
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17he93fd61ef59aa425E (type $t15) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (result i64)
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
    call $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17haa91059c63dd8dc5E)
  (func $_ZN23reflector_subscriptions7certora5token18CertoraTokenClient8transfer17h23b9f640b18c5fe1E (type $t16) (param $p0 i64) (param $p1 i64) (param $p2 i64)
    local.get $p0
    call $_ZN11soroban_sdk7address7Address12require_auth17he97f4f2ae8f99000E
    block  ;; label = @1
      local.get $p2
      i64.const -1
      i64.gt_s
      br_if 0 (;@1;)
      call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
      unreachable
    end)
  (func $_ZN11soroban_sdk7address7Address12require_auth17he97f4f2ae8f99000E (type $t17) (param $p0 i64)
    local.get $p0
    call $_ZN17soroban_env_guest5guest7address12require_auth17heac8c347e0e63eefE
    drop)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t18)
    unreachable
    unreachable)
  (func $_ZN23reflector_subscriptions7certora5token18CertoraTokenClient4burn17h111113af713dd970E (type $t19) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64)
    (local $l4 i32) (local $l5 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l4
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        local.get $p2
        i64.const 36028797018963968
        i64.add
        i64.const 72057594037927935
        i64.gt_u
        br_if 0 (;@2;)
        local.get $p2
        local.get $p2
        i64.xor
        local.get $p2
        i64.const 63
        i64.shr_s
        local.get $p3
        i64.xor
        i64.or
        i64.const 0
        i64.ne
        br_if 0 (;@2;)
        local.get $p2
        i64.const 8
        i64.shl
        i64.const 11
        i64.or
        local.set $p2
        br 1 (;@1;)
      end
      local.get $p3
      local.get $p2
      call $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17h6344a1a3ec42d4d4E
      local.set $p2
    end
    local.get $l4
    local.get $p2
    i64.store offset=8
    local.get $l4
    local.get $p1
    i64.store
    i32.const 0
    local.set $l5
    block  ;; label = @1
      loop  ;; label = @2
        block  ;; label = @3
          local.get $l5
          i32.const 16
          i32.ne
          br_if 0 (;@3;)
          i32.const 0
          local.set $l5
          block  ;; label = @4
            loop  ;; label = @5
              local.get $l5
              i32.const 16
              i32.eq
              br_if 1 (;@4;)
              local.get $l4
              i32.const 16
              i32.add
              local.get $l5
              i32.add
              local.get $l4
              local.get $l5
              i32.add
              i64.load
              i64.store
              local.get $l5
              i32.const 8
              i32.add
              local.set $l5
              br 0 (;@5;)
            end
          end
          local.get $p0
          i64.const 2678977294
          local.get $l4
          i32.const 16
          i32.add
          i32.const 2
          call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17h79c443bd00384008E
          call $_ZN17soroban_env_guest5guest4call4call17hda79ed52b11bcd56E
          i64.const 255
          i64.and
          i64.const 2
          i64.ne
          br_if 2 (;@1;)
          local.get $l4
          i32.const 32
          i32.add
          global.set $__stack_pointer
          return
        end
        local.get $l4
        i32.const 16
        i32.add
        local.get $l5
        i32.add
        i64.const 2
        i64.store
        local.get $l5
        i32.const 8
        i32.add
        local.set $l5
        br 0 (;@2;)
      end
    end
    i32.const 1049568
    local.get $l4
    i32.const 16
    i32.add
    i32.const 1049552
    call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
    unreachable)
  (func $_ZN4core6result13unwrap_failed17h472431483d5eea7fE (type $t9) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$14is_initialized17h7bd77a3fe102bc3cE (type $t20) (result i32)
    i32.const 1048652
    i32.const 5
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hba9cab496d62071bE
    i64.const 2
    call $_ZN11soroban_sdk7storage7Storage12has_internal17h0e397f3e6f3f4c21E)
  (func $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$9get_admin17he97dcfa05af55c08E (type $t7) (param $p0 i32)
    (local $l1 i32) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    i32.const 1048652
    i32.const 5
    call $_ZN11soroban_sdk7storage8Instance3get17h52ab23d73fb8ab6bE
    local.get $l1
    i64.load
    local.set $l2
    local.get $p0
    local.get $l1
    i64.load offset=8
    i64.store offset=8
    local.get $p0
    local.get $l2
    i64.store
    local.get $l1
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$7get_fee17h2069b1bb14de6c5eE (type $t6) (result i64)
    (local $l0 i32) (local $l1 i32) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    i32.const 1048657
    i32.const 8
    call $_ZN11soroban_sdk7storage8Instance3get17h4e6184aa5b3b788eE
    local.get $l0
    i32.load
    local.set $l1
    local.get $l0
    i64.load offset=8
    local.set $l2
    local.get $l0
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l2
    i64.const 0
    local.get $l1
    select)
  (func $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$7set_fee17hd45a246567d4a491E (type $t17) (param $p0 i64)
    i32.const 1048657
    i32.const 8
    local.get $p0
    call $_ZN11soroban_sdk7storage8Instance3set17hf896aec157f951feE)
  (func $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$9get_token17hb38f055530f2a96eE (type $t6) (result i64)
    (local $l0 i32) (local $l1 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    i32.const 1048665
    i32.const 5
    call $_ZN11soroban_sdk7storage8Instance3get17h52ab23d73fb8ab6bE
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
  (func $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E (type $t18)
    i32.const 1048960
    i32.const 43
    call $_ZN4core9panicking5panic17hcaca2598a27ec0fcE
    unreachable)
  (func $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$24get_last_subscription_id17h1afdcc0bc6309984E (type $t6) (result i64)
    (local $l0 i32) (local $l1 i32) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    i32.const 1048670
    i32.const 4
    call $_ZN11soroban_sdk7storage8Instance3get17h4e6184aa5b3b788eE
    local.get $l0
    i32.load
    local.set $l1
    local.get $l0
    i64.load offset=8
    local.set $l2
    local.get $l0
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l2
    i64.const 0
    local.get $l1
    select)
  (func $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$24set_last_subscription_id17haa0c8e3180408251E (type $t17) (param $p0 i64)
    i32.const 1048670
    i32.const 4
    local.get $p0
    call $_ZN11soroban_sdk7storage8Instance3set17hf896aec157f951feE)
  (func $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$16get_subscription17hcc54efa06af29242E (type $t8) (param $p0 i32) (param $p1 i64)
    (local $l2 i32) (local $l3 i32) (local $l4 i64) (local $l5 i64) (local $l6 i64) (local $l7 i64) (local $l8 i64) (local $l9 i64) (local $l10 i64) (local $l11 i64) (local $l12 i64)
    global.get $__stack_pointer
    i32.const 128
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    i32.const 2
    local.set $l3
    block  ;; label = @1
      block  ;; label = @2
        local.get $p1
        call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E
        local.tee $p1
        i64.const 1
        call $_ZN11soroban_sdk7storage7Storage12has_internal17h0e397f3e6f3f4c21E
        i32.eqz
        br_if 0 (;@2;)
        local.get $p1
        i64.const 1
        call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17hcea43a344896b5dcE
        local.set $p1
        i32.const 0
        local.set $l3
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l3
            i32.const 72
            i32.eq
            br_if 1 (;@3;)
            local.get $l2
            i32.const 32
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
        local.get $p1
        i64.const 255
        i64.and
        i64.const 76
        i64.ne
        br_if 1 (;@1;)
        local.get $p1
        i32.const 1048764
        i32.const 9
        local.get $l2
        i32.const 32
        i32.add
        i32.const 9
        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h808038e83f4d1800E
        local.get $l2
        i32.const 16
        i32.add
        local.get $l2
        i64.load offset=32
        call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E
        local.get $l2
        i32.load offset=16
        br_if 1 (;@1;)
        local.get $l2
        i64.load offset=24
        local.set $p1
        local.get $l2
        i32.const 104
        i32.add
        local.get $l2
        i64.load offset=40
        call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h31b0e2b4650a4451E
        local.get $l2
        i64.load offset=104
        i64.eqz
        i32.eqz
        br_if 1 (;@1;)
        local.get $l2
        i64.load offset=48
        local.tee $l4
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 1 (;@1;)
        local.get $l2
        i64.load offset=56
        local.tee $l5
        i64.const 255
        i64.and
        i64.const 77
        i64.ne
        br_if 1 (;@1;)
        local.get $l2
        i64.load offset=120
        local.set $l6
        local.get $l2
        i64.load offset=112
        local.set $l7
        local.get $l2
        i32.const 104
        i32.add
        local.get $l2
        i64.load offset=64
        call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h31b0e2b4650a4451E
        local.get $l2
        i64.load offset=104
        i64.eqz
        i32.eqz
        br_if 1 (;@1;)
        local.get $l2
        i64.load offset=72
        local.tee $l8
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 1 (;@1;)
        local.get $l2
        i64.load offset=120
        local.set $l9
        local.get $l2
        i64.load offset=112
        local.set $l10
        i32.const 0
        local.set $l3
        block  ;; label = @3
          block  ;; label = @4
            local.get $l8
            i64.const 32
            i64.shr_u
            i32.wrap_i64
            br_table 1 (;@3;) 0 (;@4;) 3 (;@1;)
          end
          i32.const 1
          local.set $l3
        end
        local.get $l2
        i64.load offset=80
        local.tee $l8
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 1 (;@1;)
        local.get $l2
        local.get $l2
        i64.load offset=88
        call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E
        local.get $l2
        i32.load
        br_if 1 (;@1;)
        local.get $l2
        i64.load offset=96
        local.tee $l11
        i64.const 255
        i64.and
        i64.const 72
        i64.ne
        br_if 1 (;@1;)
        local.get $l2
        i64.load offset=8
        local.set $l12
        local.get $p0
        local.get $l4
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        i32.store offset=68
        local.get $p0
        local.get $l8
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        i32.store offset=64
        local.get $p0
        local.get $l12
        i64.store offset=56
        local.get $p0
        local.get $p1
        i64.store offset=48
        local.get $p0
        local.get $l11
        i64.store offset=40
        local.get $p0
        local.get $l9
        i64.store offset=32
        local.get $p0
        local.get $l10
        i64.store offset=24
        local.get $p0
        local.get $l6
        i64.store offset=16
        local.get $p0
        local.get $l7
        i64.store offset=8
        local.get $p0
        local.get $l5
        i64.store
      end
      local.get $p0
      local.get $l3
      i32.store8 offset=72
      local.get $l2
      i32.const 128
      i32.add
      global.set $__stack_pointer
      return
    end
    unreachable
    unreachable)
  (func $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$16set_subscription17h155face630d00378E (type $t21) (param $p0 i64) (param $p1 i32)
    local.get $p0
    call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E
    local.get $p1
    call $_ZN23reflector_subscriptions5types12subscription188_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$reflector_subscriptions..types..subscription..Subscription$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17hb05340ab0a18289cE
    i64.const 1
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17haa25b294db7ef9deE
    drop)
  (func $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$23extend_subscription_ttl17h60eb70ae705e7884E (type $t21) (param $p0 i64) (param $p1 i32)
    local.get $p0
    call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E
    i64.const 1
    local.get $p1
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    local.tee $p0
    local.get $p0
    call $_ZN17soroban_env_guest5guest6ledger24extend_contract_data_ttl17h8fab322f10152870E
    drop)
  (func $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$18panic_if_not_admin17h5376458a2b095418E (type $t18)
    (local $l0 i32) (local $l1 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$9get_admin17he97dcfa05af55c08E
    block  ;; label = @1
      block  ;; label = @2
        local.get $l0
        i64.load
        local.tee $l1
        i64.eqz
        br_if 0 (;@2;)
        local.get $l1
        i32.wrap_i64
        i32.eqz
        br_if 1 (;@1;)
        local.get $l0
        i64.load offset=8
        call $_ZN17soroban_env_guest5guest7address12require_auth17heac8c347e0e63eefE
        drop
        local.get $l0
        i32.const 16
        i32.add
        global.set $__stack_pointer
        return
      end
      i64.const 4294967299
      call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
      unreachable
      unreachable
    end
    call $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E
    unreachable)
  (func $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E (type $t17) (param $p0 i64)
    local.get $p0
    call $_ZN17soroban_env_guest5guest7context15fail_with_error17hada9d6da67b2f63eE
    drop)
  (func $_ZN93_$LT$u128$u20$as$u20$reflector_subscriptions..extensions..u128_extensions..U128Extensions$GT$4sqrt17hdb5774cc036c6bf0E (type $t22) (param $p0 i32) (param $p1 i64) (param $p2 i64)
    (local $l3 i32) (local $l4 i64) (local $l5 i64) (local $l6 i64) (local $l7 i64) (local $l8 i64) (local $l9 i32) (local $l10 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        local.get $p1
        local.get $p2
        i64.or
        i64.eqz
        i32.eqz
        br_if 0 (;@2;)
        i64.const 0
        local.set $l4
        i64.const 0
        local.set $l5
        br 1 (;@1;)
      end
      local.get $l3
      i64.const 1
      i64.const 0
      local.get $p2
      i64.clz
      local.get $p1
      i64.clz
      i64.const 64
      i64.add
      local.get $p2
      i64.const 0
      i64.ne
      select
      i32.wrap_i64
      i32.const -1
      i32.xor
      i32.const 126
      i32.and
      call $__ashlti3
      local.get $l3
      i32.const 8
      i32.add
      i64.load
      local.set $l6
      local.get $l3
      i64.load
      local.set $l7
      i64.const 0
      local.set $l4
      i64.const 0
      local.set $l5
      loop  ;; label = @2
        local.get $l7
        local.get $l6
        i64.or
        i64.eqz
        br_if 1 (;@1;)
        block  ;; label = @3
          local.get $l4
          local.get $l7
          i64.add
          local.tee $l8
          local.get $l4
          i64.lt_u
          local.tee $l9
          local.get $l5
          local.get $l6
          i64.add
          local.get $l9
          i64.extend_i32_u
          i64.add
          local.tee $l10
          local.get $l5
          i64.lt_u
          local.get $l10
          local.get $l5
          i64.eq
          select
          br_if 0 (;@3;)
          local.get $p2
          i64.const 0
          local.get $l10
          local.get $p1
          local.get $l8
          i64.lt_u
          local.get $p2
          local.get $l10
          i64.lt_u
          local.get $p2
          local.get $l10
          i64.eq
          select
          local.tee $l9
          select
          i64.sub
          local.get $p1
          i64.const 0
          local.get $l8
          local.get $l9
          select
          local.tee $l10
          i64.lt_u
          i64.extend_i32_u
          i64.sub
          local.set $p2
          i64.const 0
          local.get $l6
          local.get $l9
          select
          local.get $l5
          i64.const 1
          i64.shr_u
          i64.add
          i64.const 0
          local.get $l7
          local.get $l9
          select
          local.tee $l8
          local.get $l4
          i64.const 1
          i64.shr_u
          local.get $l5
          i64.const 63
          i64.shl
          i64.or
          i64.add
          local.tee $l4
          local.get $l8
          i64.lt_u
          i64.extend_i32_u
          i64.add
          local.set $l5
          local.get $p1
          local.get $l10
          i64.sub
          local.set $p1
          local.get $l7
          i64.const 2
          i64.shr_u
          local.get $l6
          i64.const 62
          i64.shl
          i64.or
          local.set $l7
          local.get $l6
          i64.const 2
          i64.shr_u
          local.set $l6
          br 1 (;@2;)
        end
      end
      call $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E
      unreachable
    end
    local.get $p0
    local.get $l4
    i64.store
    local.get $p0
    local.get $l5
    i64.store offset=8
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E (type $t18)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN23reflector_subscriptions8calc_fee17h9c62d7e4ca088a5fE (type $t23) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i32) (result i64)
    (local $l4 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l4
    global.set $__stack_pointer
    local.get $l4
    local.get $p0
    local.get $p3
    call $_ZN23reflector_subscriptions17calc_hearbeat_fee17hb280591977179836E
    i64.const 0
    local.get $p1
    local.get $p2
    call $_ZN23reflector_subscriptions22calc_complexity_factor17hbf0f6157f2b16fefE
    i64.const 0
    call $__multi3
    block  ;; label = @1
      local.get $l4
      i64.load offset=8
      i64.const 0
      i64.ne
      br_if 0 (;@1;)
      local.get $l4
      i64.load
      local.set $p2
      local.get $l4
      i32.const 16
      i32.add
      global.set $__stack_pointer
      local.get $p2
      return
    end
    call $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E
    unreachable)
  (func $_ZN23reflector_subscriptions17calc_hearbeat_fee17hb280591977179836E (type $t24) (param $p0 i64) (param $p1 i32) (result i64)
    (local $l2 i32) (local $l3 i32) (local $l4 i64) (local $l5 i64) (local $l6 i32)
    global.get $__stack_pointer
    i32.const 96
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    i32.const 24
    i32.add
    local.set $l3
    local.get $p0
    local.set $l4
    i64.const 0
    local.set $l5
    i32.const 1
    local.set $l6
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l6
            i32.const 1
            i32.and
            i32.eqz
            br_if 1 (;@3;)
            local.get $l2
            local.get $l5
            i64.const 0
            local.get $l4
            i64.const 0
            call $__multi3
            local.get $l2
            i32.const 16
            i32.add
            local.get $l4
            i64.const 0
            local.get $l4
            i64.const 0
            call $__multi3
            local.get $l5
            local.get $l2
            i64.load offset=8
            i64.or
            i64.const 0
            i64.ne
            local.get $l3
            i64.load
            local.tee $l4
            local.get $l2
            i64.load
            local.tee $l5
            local.get $l5
            i64.add
            i64.add
            local.tee $l5
            local.get $l4
            i64.lt_u
            i32.or
            br_if 2 (;@2;)
            local.get $l2
            i64.load offset=16
            local.set $l4
            i32.const 0
            local.set $l6
            br 0 (;@4;)
          end
        end
        local.get $l2
        i32.const 64
        i32.add
        local.get $l5
        i64.const 0
        i64.const 120
        i64.const 0
        call $__multi3
        local.get $l2
        i32.const 80
        i32.add
        local.get $l4
        i64.const 0
        i64.const 120
        i64.const 0
        call $__multi3
        local.get $l2
        i64.load offset=72
        i64.const 0
        i64.ne
        local.get $l2
        i32.const 88
        i32.add
        i64.load
        local.tee $l4
        local.get $l2
        i64.load offset=64
        i64.add
        local.tee $l5
        local.get $l4
        i64.lt_u
        i32.or
        br_if 0 (;@2;)
        local.get $p1
        br_if 1 (;@1;)
      end
      call $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E
      unreachable
    end
    local.get $l2
    i32.const 32
    i32.add
    local.get $l2
    i64.load offset=80
    local.get $l5
    local.get $p1
    i64.extend_i32_u
    i64.const 0
    call $__udivti3
    local.get $l2
    i32.const 48
    i32.add
    local.get $l2
    i64.load offset=32
    local.get $l2
    i32.const 40
    i32.add
    i64.load
    call $_ZN93_$LT$u128$u20$as$u20$reflector_subscriptions..extensions..u128_extensions..U128Extensions$GT$4sqrt17hdb5774cc036c6bf0E
    local.get $l2
    i64.load offset=48
    local.set $l4
    local.get $l2
    i32.const 96
    i32.add
    global.set $__stack_pointer
    local.get $l4
    local.get $p0
    local.get $l4
    local.get $p0
    i64.gt_u
    select)
  (func $_ZN23reflector_subscriptions22calc_complexity_factor17hbf0f6157f2b16fefE (type $t3) (param $p0 i64) (param $p1 i64) (result i64)
    i64.const 1
    i64.const 2
    local.get $p0
    local.get $p1
    call $_ZN17soroban_env_guest5guest7context7obj_cmp17hb0d21973d6fefaacE
    i64.eqz
    select)
  (func $_ZN23reflector_subscriptions24panic_if_not_initialized17h9f5369fdfb879af3E (type $t18)
    block  ;; label = @1
      call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$14is_initialized17h7bd77a3fe102bc3cE
      br_if 0 (;@1;)
      i64.const 12884901891
      call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
      unreachable
      unreachable
    end)
  (func $_ZN23reflector_subscriptions7deposit17hea0769815d695068E (type $t25) (param $p0 i64) (param $p1 i64)
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$9get_token17hb38f055530f2a96eE
    drop
    call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17hcc67655a7974e4f6E
    drop
    local.get $p0
    local.get $p1
    i64.const 0
    call $_ZN23reflector_subscriptions7certora5token18CertoraTokenClient8transfer17h23b9f640b18c5fe1E)
  (func $_ZN23reflector_subscriptions4burn17h7418d947fc3289c1E (type $t25) (param $p0 i64) (param $p1 i64)
    block  ;; label = @1
      local.get $p0
      local.get $p1
      i64.gt_u
      br_if 0 (;@1;)
      call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$9get_token17hb38f055530f2a96eE
      call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17hcc67655a7974e4f6E
      local.get $p0
      i64.const 0
      call $_ZN23reflector_subscriptions7certora5token18CertoraTokenClient4burn17h111113af713dd970E
      return
    end
    i64.const 17179869187
    call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
    unreachable
    unreachable)
  (func $_ZN23reflector_subscriptions3now17h417906866f151dc1E (type $t6) (result i64)
    (local $l0 i32) (local $l1 i64) (local $l2 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        call $_ZN17soroban_env_guest5guest7context20get_ledger_timestamp17h1842398ca4defda9E
        local.tee $l1
        i32.wrap_i64
        i32.const 255
        i32.and
        local.tee $l2
        i32.const 64
        i32.eq
        br_if 0 (;@2;)
        block  ;; label = @3
          local.get $l2
          i32.const 6
          i32.ne
          br_if 0 (;@3;)
          local.get $l1
          i64.const 8
          i64.shr_u
          local.set $l1
          br 2 (;@1;)
        end
        i32.const 1049568
        local.get $l0
        i32.const 24
        i32.add
        i32.const 1049612
        call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
        unreachable
      end
      local.get $l1
      call $_ZN17soroban_env_guest5guest3int10obj_to_u6417h04c12c1e1e50ea61E
      local.set $l1
    end
    local.get $l0
    i32.const 8
    i32.add
    local.get $l1
    i64.const 0
    i64.const 1000
    i64.const 0
    call $__multi3
    block  ;; label = @1
      local.get $l0
      i64.load offset=16
      i64.const 0
      i64.ne
      br_if 0 (;@1;)
      local.get $l0
      i64.load offset=8
      local.set $l1
      local.get $l0
      i32.const 32
      i32.add
      global.set $__stack_pointer
      local.get $l1
      return
    end
    call $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E
    unreachable)
  (func $_ZN23reflector_subscriptions20calc_ledgers_to_live17h1520017dee4a92d6E (type $t11) (param $p0 i64) (param $p1 i64) (result i32)
    (local $l2 i64) (local $l3 i32)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p1
        local.get $p0
        i64.add
        local.tee $l2
        local.get $p1
        i64.lt_u
        br_if 0 (;@2;)
        local.get $l2
        i64.eqz
        br_if 0 (;@2;)
        local.get $p0
        i64.eqz
        br_if 0 (;@2;)
        local.get $l2
        i64.const -1
        i64.add
        local.get $p0
        i64.div_u
        i32.wrap_i64
        local.tee $l3
        i32.const 1
        local.get $l3
        i32.const 1
        i32.gt_u
        select
        i64.extend_i32_u
        i64.const 17280
        i64.mul
        local.tee $p0
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        br_if 0 (;@2;)
        call $_ZN17soroban_env_guest5guest7context19get_ledger_sequence17hc627523f88a30ab8E
        local.set $p1
        call $_ZN17soroban_env_guest5guest7context25get_max_live_until_ledger17h77a0bfec84a4f373E
        i64.const 32
        i64.shr_u
        local.tee $l2
        local.get $p1
        i64.const 32
        i64.shr_u
        local.tee $p1
        i64.lt_u
        br_if 0 (;@2;)
        local.get $p0
        i32.wrap_i64
        local.tee $l3
        local.get $l2
        i32.wrap_i64
        local.get $p1
        i32.wrap_i64
        i32.sub
        i32.le_u
        br_if 1 (;@1;)
        i64.const 17179869187
        call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
        unreachable
        unreachable
      end
      call $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E
      unreachable
    end
    local.get $l3)
  (func $_ZN23reflector_subscriptions13spec_entrypt317h8e1378403221ebc2E (type $t17) (param $p0 i64)
    (local $l1 i32) (local $l2 i64) (local $l3 i32)
    global.get $__stack_pointer
    i32.const 160
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    call $_ZN3cvt14CVT_nondet_u6417h5a4926c234f14ba3E
    local.set $l2
    local.get $l1
    i32.const 80
    i32.add
    local.get $p0
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$16get_subscription17hcc54efa06af29242E
    block  ;; label = @1
      local.get $l1
      i32.load8_u offset=152
      i32.const 2
      i32.eq
      br_if 0 (;@1;)
      block  ;; label = @2
        local.get $l1
        local.get $l1
        i32.const 80
        i32.add
        i32.const 80
        call $memcpy
        local.tee $l1
        i64.load offset=48
        local.get $l2
        i64.ge_u
        br_if 0 (;@2;)
        local.get $l1
        i32.const 1
        i32.store8 offset=72
      end
      local.get $p0
      local.get $l1
      call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$16set_subscription17h155face630d00378E
      local.get $l1
      i32.const 80
      i32.add
      local.get $p0
      call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$16get_subscription17hcc54efa06af29242E
      local.get $l1
      i32.load8_u offset=152
      local.tee $l3
      i32.const 2
      i32.eq
      br_if 0 (;@1;)
      local.get $l1
      i64.load offset=128
      local.get $l2
      i64.ge_u
      local.get $l3
      i32.const 0
      i32.ne
      i32.or
      call $_ZN3cvt10CVT_assert17hfb9b9689c8fded82E
      local.get $l1
      i32.const 160
      i32.add
      global.set $__stack_pointer
      return
    end
    call $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E
    unreachable)
  (func $_ZN3cvt14CVT_nondet_u6417h5a4926c234f14ba3E (type $t6) (result i64)
    call $CVT_nondet_u64_c)
  (func $_ZN3cvt10CVT_assert17hfb9b9689c8fded82E (type $t7) (param $p0 i32)
    local.get $p0
    call $CVT_assert_c)
  (func $sunbeam_entrypt (type $t18)
    call $_ZN3cvt14CVT_nondet_u6417h5a4926c234f14ba3E
    call $_ZN23reflector_subscriptions13spec_entrypt317h8e1378403221ebc2E)
  (func $config (type $t2) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i32) (local $l3 i64) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    i32.const 0
    local.set $l2
    block  ;; label = @1
      loop  ;; label = @2
        local.get $l2
        i32.const 24
        i32.eq
        br_if 1 (;@1;)
        local.get $l1
        i32.const 24
        i32.add
        local.get $l2
        i32.add
        i64.const 2
        i64.store
        local.get $l2
        i32.const 8
        i32.add
        local.set $l2
        br 0 (;@2;)
      end
    end
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i64.const 255
        i64.and
        i64.const 76
        i64.ne
        br_if 0 (;@2;)
        local.get $p0
        i32.const 1048840
        i32.const 3
        local.get $l1
        i32.const 24
        i32.add
        i32.const 3
        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h808038e83f4d1800E
        local.get $l1
        i64.load offset=24
        local.tee $p0
        i64.const 255
        i64.and
        i64.const 77
        i64.ne
        br_if 0 (;@2;)
        local.get $l1
        i32.const 8
        i32.add
        local.get $l1
        i64.load offset=32
        call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E
        local.get $l1
        i64.load offset=8
        i32.wrap_i64
        br_if 0 (;@2;)
        local.get $l1
        i64.load offset=40
        local.tee $l3
        i64.const 255
        i64.and
        i64.const 77
        i64.ne
        br_if 0 (;@2;)
        local.get $l1
        i64.load offset=16
        local.set $l4
        local.get $p0
        call $_ZN17soroban_env_guest5guest7address12require_auth17heac8c347e0e63eefE
        drop
        call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$14is_initialized17h7bd77a3fe102bc3cE
        i32.eqz
        br_if 1 (;@1;)
        i64.const 3
        call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
      end
      unreachable
      unreachable
    end
    i32.const 1048652
    i32.const 5
    local.get $p0
    call $_ZN11soroban_sdk7storage8Instance3set17h6dc43fc876a1ad1aE
    local.get $l4
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$7set_fee17hd45a246567d4a491E
    i32.const 1048665
    i32.const 5
    local.get $l3
    call $_ZN11soroban_sdk7storage8Instance3set17h6dc43fc876a1ad1aE
    i64.const 0
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$24set_last_subscription_id17haa0c8e3180408251E
    local.get $l1
    i32.const 48
    i32.add
    global.set $__stack_pointer
    i64.const 2)
  (func $set_fee (type $t2) (param $p0 i64) (result i64)
    (local $l1 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    local.get $p0
    call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E
    block  ;; label = @1
      local.get $l1
      i64.load
      i32.wrap_i64
      i32.eqz
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $l1
    i64.load offset=8
    local.set $p0
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$18panic_if_not_admin17h5376458a2b095418E
    local.get $p0
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$7set_fee17hd45a246567d4a491E
    local.get $l1
    i32.const 16
    i32.add
    global.set $__stack_pointer
    i64.const 2)
  (func $trigger (type $t3) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32) (local $l3 i32) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 64
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    i32.const 16
    i32.add
    local.get $p0
    call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E
    block  ;; label = @1
      local.get $l2
      i64.load offset=16
      i32.wrap_i64
      br_if 0 (;@1;)
      local.get $l2
      i64.load offset=24
      local.set $p0
      local.get $l2
      local.get $p1
      call $_ZN155_$LT$soroban_sdk..bytes..BytesN$LT$_$GT$$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0092c8c1267dfcebE
      local.get $l2
      i64.load
      i32.wrap_i64
      br_if 0 (;@1;)
      local.get $l2
      i64.load offset=8
      local.set $p1
      call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$18panic_if_not_admin17h5376458a2b095418E
      local.get $l2
      i64.const 4170028882079688974
      i64.store offset=40
      local.get $l2
      i64.const 4011225584324392718
      i64.store offset=32
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
              local.get $l2
              i32.const 48
              i32.add
              local.get $l3
              i32.add
              local.get $l2
              i32.const 32
              i32.add
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
          local.get $l2
          i32.const 48
          i32.add
          i32.const 2
          call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17h79c443bd00384008E
          local.set $l4
          local.get $p0
          call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E
          local.set $p0
          local.get $l2
          local.get $p1
          i64.store offset=56
          local.get $l2
          local.get $p0
          i64.store offset=48
          local.get $l4
          local.get $l2
          i32.const 48
          i32.add
          i32.const 2
          call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17h79c443bd00384008E
          call $_ZN17soroban_env_guest5guest7context14contract_event17ha9a5af34bd21bbfcE
          drop
          local.get $l2
          i32.const 64
          i32.add
          global.set $__stack_pointer
          i64.const 2
          return
        end
        local.get $l2
        i32.const 48
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
  (func $_ZN155_$LT$soroban_sdk..bytes..BytesN$LT$_$GT$$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0092c8c1267dfcebE (type $t8) (param $p0 i32) (param $p1 i64)
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
      call $_ZN17soroban_env_guest5guest3buf9bytes_len17h5f2677f709d7063cE
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
  (func $charge (type $t2) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i64) (local $l3 i64) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 192
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    i32.const 16
    i32.add
    local.get $p0
    call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E
    block  ;; label = @1
      block  ;; label = @2
        local.get $l1
        i32.load offset=16
        br_if 0 (;@2;)
        local.get $l1
        i64.load offset=24
        local.set $p0
        call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$18panic_if_not_admin17h5376458a2b095418E
        call $_ZN23reflector_subscriptions3now17h417906866f151dc1E
        local.set $l2
        local.get $l1
        i32.const 32
        i32.add
        local.get $p0
        call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$16get_subscription17hcc54efa06af29242E
        block  ;; label = @3
          local.get $l1
          i32.load8_u offset=104
          i32.const 2
          i32.eq
          br_if 0 (;@3;)
          local.get $l1
          i32.const 112
          i32.add
          local.get $l1
          i32.const 32
          i32.add
          i32.const 80
          call $memcpy
          drop
          local.get $l2
          local.get $l1
          i64.load offset=168
          local.tee $l3
          i64.lt_u
          br_if 2 (;@1;)
          local.get $l2
          local.get $l3
          i64.sub
          local.tee $l3
          i64.const 86400000
          i64.lt_u
          br_if 0 (;@3;)
          local.get $l1
          local.get $l3
          i64.const 86400000
          i64.div_u
          i64.const 0
          call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$7get_fee17h2069b1bb14de6c5eE
          local.get $l1
          i64.load offset=128
          local.get $l1
          i64.load offset=144
          local.get $l1
          i32.load offset=180
          call $_ZN23reflector_subscriptions8calc_fee17h9c62d7e4ca088a5fE
          local.tee $l4
          i64.const 0
          call $__multi3
          local.get $l1
          i64.load offset=8
          i64.eqz
          i32.eqz
          br_if 2 (;@1;)
          local.get $l1
          i64.load
          local.set $l3
          local.get $l1
          local.get $l2
          i64.store offset=168
          local.get $l1
          local.get $l1
          i64.load offset=160
          local.tee $l2
          local.get $l2
          local.get $l3
          local.get $l2
          local.get $l3
          i64.lt_u
          select
          local.tee $l2
          i64.sub
          local.tee $l3
          i64.store offset=160
          block  ;; label = @4
            local.get $l3
            local.get $l4
            i64.ge_u
            br_if 0 (;@4;)
            local.get $l1
            i32.const 1
            i32.store8 offset=184
          end
          local.get $p0
          local.get $l1
          i32.const 112
          i32.add
          call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$16set_subscription17h155face630d00378E
          local.get $l2
          i64.eqz
          br_if 0 (;@3;)
          call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$9get_token17hb38f055530f2a96eE
          call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17hcc67655a7974e4f6E
          local.get $l2
          i64.const 0
          call $_ZN23reflector_subscriptions7certora5token18CertoraTokenClient4burn17h111113af713dd970E
        end
        local.get $l1
        i32.const 192
        i32.add
        global.set $__stack_pointer
        i64.const 2
        return
      end
      unreachable
      unreachable
    end
    call $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E
    unreachable)
  (func $update_contract (type $t2) (param $p0 i64) (result i64)
    (local $l1 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    local.get $p0
    call $_ZN155_$LT$soroban_sdk..bytes..BytesN$LT$_$GT$$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0092c8c1267dfcebE
    block  ;; label = @1
      local.get $l1
      i64.load
      i32.wrap_i64
      i32.eqz
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $l1
    i64.load offset=8
    local.set $p0
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$18panic_if_not_admin17h5376458a2b095418E
    local.get $p0
    call $_ZN17soroban_env_guest5guest6ledger28update_current_contract_wasm17hf31ebfa6a5376f4eE
    drop
    local.get $l1
    i32.const 16
    i32.add
    global.set $__stack_pointer
    i64.const 2)
  (func $create_subscription (type $t3) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32) (local $l3 i32) (local $l4 i64) (local $l5 i64) (local $l6 i64) (local $l7 i64) (local $l8 i64) (local $l9 i64) (local $l10 i64) (local $l11 i64) (local $l12 i64) (local $l13 i64) (local $l14 i32)
    global.get $__stack_pointer
    i32.const 304
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    i32.const 0
    local.set $l3
    block  ;; label = @1
      loop  ;; label = @2
        local.get $l3
        i32.const 48
        i32.eq
        br_if 1 (;@1;)
        local.get $l2
        i32.const 216
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
      local.get $p0
      i64.const 255
      i64.and
      i64.const 76
      i64.ne
      br_if 0 (;@1;)
      local.get $p0
      i32.const 1048864
      i32.const 6
      local.get $l2
      i32.const 216
      i32.add
      i32.const 6
      call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h808038e83f4d1800E
      local.get $l2
      i32.const 24
      i32.add
      local.get $l2
      i64.load offset=216
      call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h31b0e2b4650a4451E
      local.get $l2
      i64.load offset=24
      i64.eqz
      i32.eqz
      br_if 0 (;@1;)
      local.get $l2
      i64.load offset=224
      local.tee $l4
      i64.const 255
      i64.and
      i64.const 4
      i64.ne
      br_if 0 (;@1;)
      local.get $l2
      i64.load offset=232
      local.tee $p0
      i64.const 255
      i64.and
      i64.const 77
      i64.ne
      br_if 0 (;@1;)
      local.get $l2
      i64.load offset=40
      local.set $l5
      local.get $l2
      i64.load offset=32
      local.set $l6
      local.get $l2
      i32.const 24
      i32.add
      local.get $l2
      i64.load offset=240
      call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h31b0e2b4650a4451E
      local.get $l2
      i64.load offset=24
      i64.eqz
      i32.eqz
      br_if 0 (;@1;)
      local.get $l2
      i64.load offset=248
      local.tee $l7
      i64.const 255
      i64.and
      i64.const 4
      i64.ne
      br_if 0 (;@1;)
      local.get $l2
      i64.load offset=256
      local.tee $l8
      i64.const 255
      i64.and
      i64.const 72
      i64.ne
      br_if 0 (;@1;)
      local.get $l2
      i64.load offset=40
      local.set $l9
      local.get $l2
      i64.load offset=32
      local.set $l10
      local.get $l2
      i32.const 8
      i32.add
      local.get $p1
      call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E
      local.get $l2
      i32.load offset=8
      br_if 0 (;@1;)
      local.get $l2
      i64.load offset=16
      local.set $l11
      call $_ZN23reflector_subscriptions24panic_if_not_initialized17h9f5369fdfb879af3E
      local.get $p0
      call $_ZN17soroban_env_guest5guest7address12require_auth17heac8c347e0e63eefE
      drop
      block  ;; label = @2
        call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$7get_fee17h2069b1bb14de6c5eE
        local.get $l5
        local.get $l9
        local.get $l4
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        local.tee $l3
        call $_ZN23reflector_subscriptions8calc_fee17h9c62d7e4ca088a5fE
        local.tee $l12
        i64.const 0
        i64.lt_s
        br_if 0 (;@2;)
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              local.get $l11
              local.get $l12
              i64.const 1
              i64.shl
              local.tee $l13
              i64.lt_u
              br_if 0 (;@5;)
              local.get $l3
              i32.const 5
              i32.lt_u
              br_if 1 (;@4;)
              block  ;; label = @6
                local.get $l7
                i64.const 32
                i64.shr_u
                i32.wrap_i64
                local.tee $l14
                i32.const -10001
                i32.add
                i32.const -10000
                i32.ge_u
                br_if 0 (;@6;)
                i64.const 25769803779
                call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
                br 5 (;@1;)
              end
              local.get $l8
              call $_ZN17soroban_env_guest5guest3buf9bytes_len17h5f2677f709d7063cE
              i64.const 32
              i64.shr_u
              i32.wrap_i64
              i32.const 2048
              i32.gt_u
              br_if 2 (;@3;)
              local.get $p0
              local.get $l11
              call $_ZN23reflector_subscriptions7deposit17hea0769815d695068E
              local.get $l13
              local.get $l11
              call $_ZN23reflector_subscriptions4burn17h7418d947fc3289c1E
              call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$24get_last_subscription_id17h1afdcc0bc6309984E
              i64.const 1
              i64.add
              local.tee $p1
              i64.eqz
              br_if 3 (;@2;)
              call $_ZN23reflector_subscriptions3now17h417906866f151dc1E
              local.set $l4
              local.get $l2
              local.get $l3
              i32.store offset=180
              local.get $l2
              local.get $l14
              i32.store offset=176
              local.get $l2
              local.get $l9
              i64.store offset=144
              local.get $l2
              local.get $l10
              i64.store offset=136
              local.get $l2
              local.get $l5
              i64.store offset=128
              local.get $l2
              local.get $l6
              i64.store offset=120
              local.get $l2
              local.get $p0
              i64.store offset=112
              local.get $l2
              i32.const 0
              i32.store8 offset=184
              local.get $l2
              local.get $l11
              local.get $l13
              i64.sub
              local.tee $l11
              i64.store offset=160
              local.get $l2
              local.get $l8
              i64.store offset=152
              local.get $l2
              local.get $l4
              i64.store offset=168
              local.get $p1
              local.get $l2
              i32.const 112
              i32.add
              call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$16set_subscription17h155face630d00378E
              local.get $p1
              call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$24set_last_subscription_id17haa0c8e3180408251E
              local.get $p1
              local.get $l12
              local.get $l11
              call $_ZN23reflector_subscriptions20calc_ledgers_to_live17h1520017dee4a92d6E
              call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$23extend_subscription_ttl17h60eb70ae705e7884E
              local.get $l2
              local.get $p0
              i64.store offset=208
              local.get $l2
              i64.const 718988725889294
              i64.store offset=200
              local.get $l2
              i64.const 4011225584324392718
              i64.store offset=192
              local.get $l2
              local.get $l3
              i32.store offset=292
              local.get $l2
              local.get $l14
              i32.store offset=288
              local.get $l2
              local.get $l9
              i64.store offset=256
              local.get $l2
              local.get $l10
              i64.store offset=248
              local.get $l2
              local.get $l5
              i64.store offset=240
              local.get $l2
              local.get $l6
              i64.store offset=232
              local.get $l2
              local.get $p0
              i64.store offset=224
              local.get $l2
              local.get $p1
              i64.store offset=216
              local.get $l2
              i32.const 0
              i32.store8 offset=296
              local.get $l2
              local.get $l11
              i64.store offset=272
              local.get $l2
              local.get $l8
              i64.store offset=264
              local.get $l2
              local.get $l4
              i64.store offset=280
              local.get $l2
              i32.const 192
              i32.add
              call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h73fad27a55c2a023E
              local.get $l2
              i32.const 216
              i32.add
              call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17he412710998833677E
              call $_ZN17soroban_env_guest5guest7context14contract_event17ha9a5af34bd21bbfcE
              drop
              local.get $l2
              i32.const 0
              i32.store8 offset=104
              local.get $l2
              local.get $l3
              i32.store offset=100
              local.get $l2
              local.get $l14
              i32.store offset=96
              local.get $l2
              local.get $l4
              i64.store offset=88
              local.get $l2
              local.get $l11
              i64.store offset=80
              local.get $l2
              local.get $l8
              i64.store offset=72
              local.get $l2
              local.get $l9
              i64.store offset=64
              local.get $l2
              local.get $l10
              i64.store offset=56
              local.get $l2
              local.get $l5
              i64.store offset=48
              local.get $l2
              local.get $l6
              i64.store offset=40
              local.get $l2
              local.get $p0
              i64.store offset=32
              local.get $l2
              local.get $p1
              i64.store offset=24
              local.get $l2
              i32.const 24
              i32.add
              call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17he412710998833677E
              local.set $p0
              local.get $l2
              i32.const 304
              i32.add
              global.set $__stack_pointer
              local.get $p0
              return
            end
            i64.const 17179869187
            call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
            br 3 (;@1;)
          end
          i64.const 21474836483
          call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
          br 2 (;@1;)
        end
        i64.const 30064771075
        call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
        br 1 (;@1;)
      end
      call $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E
      unreachable
    end
    unreachable
    unreachable)
  (func $deposit (type $t4) (param $p0 i64) (param $p1 i64) (param $p2 i64) (result i64)
    (local $l3 i32) (local $l4 i64) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 256
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i64.const 255
        i64.and
        i64.const 77
        i64.ne
        br_if 0 (;@2;)
        local.get $l3
        i32.const 16
        i32.add
        local.get $p1
        call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E
        local.get $l3
        i32.load offset=16
        br_if 0 (;@2;)
        local.get $l3
        i64.load offset=24
        local.set $l4
        local.get $l3
        local.get $p2
        call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E
        local.get $l3
        i32.load
        br_if 0 (;@2;)
        local.get $l3
        i64.load offset=8
        local.set $p1
        call $_ZN23reflector_subscriptions24panic_if_not_initialized17h9f5369fdfb879af3E
        local.get $p0
        call $_ZN17soroban_env_guest5guest7address12require_auth17heac8c347e0e63eefE
        drop
        block  ;; label = @3
          local.get $p1
          i64.const 0
          i64.ne
          br_if 0 (;@3;)
          i64.const 17179869187
          call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
          br 1 (;@2;)
        end
        local.get $l3
        i32.const 136
        i32.add
        local.get $l4
        call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$16get_subscription17hcc54efa06af29242E
        local.get $l3
        i32.load8_u offset=208
        i32.const 2
        i32.ne
        br_if 1 (;@1;)
        i64.const 8589934595
        call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
      end
      unreachable
      unreachable
    end
    local.get $l3
    i32.const 32
    i32.add
    local.get $l3
    i32.const 136
    i32.add
    i32.const 80
    call $memcpy
    drop
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$7get_fee17h2069b1bb14de6c5eE
    local.get $l3
    i64.load offset=48
    local.get $l3
    i64.load offset=64
    local.get $l3
    i32.load offset=100
    call $_ZN23reflector_subscriptions8calc_fee17h9c62d7e4ca088a5fE
    local.set $p2
    local.get $p0
    local.get $p1
    call $_ZN23reflector_subscriptions7deposit17hea0769815d695068E
    block  ;; label = @1
      local.get $l3
      i64.load offset=80
      local.tee $l5
      local.get $p1
      i64.add
      local.tee $p0
      local.get $l5
      i64.lt_u
      br_if 0 (;@1;)
      local.get $l3
      local.get $p0
      i64.store offset=80
      block  ;; label = @2
        local.get $l3
        i32.load8_u offset=104
        i32.eqz
        br_if 0 (;@2;)
        local.get $p2
        local.get $p1
        call $_ZN23reflector_subscriptions4burn17h7418d947fc3289c1E
        local.get $p0
        local.get $p2
        i64.lt_u
        br_if 1 (;@1;)
        local.get $l3
        i32.const 0
        i32.store8 offset=104
        local.get $l3
        local.get $p0
        local.get $p2
        i64.sub
        local.tee $p0
        i64.store offset=80
      end
      local.get $l4
      local.get $l3
      i32.const 32
      i32.add
      call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$16set_subscription17h155face630d00378E
      local.get $l4
      local.get $p2
      local.get $p0
      call $_ZN23reflector_subscriptions20calc_ledgers_to_live17h1520017dee4a92d6E
      call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$23extend_subscription_ttl17h60eb70ae705e7884E
      local.get $l3
      local.get $l3
      i64.load offset=32
      i64.store offset=128
      local.get $l3
      i64.const 3002596074819594510
      i64.store offset=120
      local.get $l3
      i64.const 4011225584324392718
      i64.store offset=112
      local.get $l3
      i32.const 136
      i32.add
      local.get $l3
      i32.const 32
      i32.add
      i32.const 80
      call $memcpy
      drop
      local.get $l3
      local.get $p1
      i64.store offset=224
      local.get $l3
      local.get $l4
      i64.store offset=216
      local.get $l3
      i32.const 112
      i32.add
      call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h73fad27a55c2a023E
      local.set $p0
      local.get $l4
      call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E
      local.set $l4
      local.get $l3
      i32.const 136
      i32.add
      call $_ZN23reflector_subscriptions5types12subscription188_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$reflector_subscriptions..types..subscription..Subscription$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17hb05340ab0a18289cE
      local.set $p2
      local.get $l3
      local.get $p1
      call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E
      i64.store offset=248
      local.get $l3
      local.get $p2
      i64.store offset=240
      local.get $l3
      local.get $l4
      i64.store offset=232
      local.get $p0
      local.get $l3
      i32.const 232
      i32.add
      i32.const 3
      call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17h79c443bd00384008E
      call $_ZN17soroban_env_guest5guest7context14contract_event17ha9a5af34bd21bbfcE
      drop
      local.get $l3
      i32.const 256
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    call $_ZN4core9panicking11panic_const23panic_const_div_by_zero17he931327ad9ba09d8E
    unreachable)
  (func $cancel (type $t2) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i32) (local $l3 i64) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 96
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    local.get $p0
    call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E
    block  ;; label = @1
      block  ;; label = @2
        local.get $l1
        i32.load
        br_if 0 (;@2;)
        local.get $l1
        i64.load offset=8
        local.set $p0
        call $_ZN23reflector_subscriptions24panic_if_not_initialized17h9f5369fdfb879af3E
        local.get $l1
        i32.const 16
        i32.add
        local.get $p0
        call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$16get_subscription17hcc54efa06af29242E
        block  ;; label = @3
          local.get $l1
          i32.load8_u offset=88
          local.tee $l2
          i32.const 2
          i32.ne
          br_if 0 (;@3;)
          i64.const 8589934595
          call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
          br 1 (;@2;)
        end
        local.get $l1
        i64.load offset=64
        local.set $l3
        local.get $l1
        i64.load offset=16
        local.tee $l4
        call $_ZN17soroban_env_guest5guest7address12require_auth17heac8c347e0e63eefE
        drop
        local.get $l2
        i32.eqz
        br_if 1 (;@1;)
        i64.const 34359738371
        call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
      end
      unreachable
      unreachable
    end
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$9get_token17hb38f055530f2a96eE
    drop
    call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17hcc67655a7974e4f6E
    local.get $l3
    i64.const 0
    call $_ZN23reflector_subscriptions7certora5token18CertoraTokenClient8transfer17h23b9f640b18c5fe1E
    local.get $p0
    call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E
    i64.const 1
    call $_ZN17soroban_env_guest5guest6ledger17del_contract_data17hef3bcb945e85743fE
    drop
    local.get $l1
    local.get $l4
    i64.store offset=32
    local.get $l1
    i64.const 2925996338310719758
    i64.store offset=24
    local.get $l1
    i64.const 4011225584324392718
    i64.store offset=16
    local.get $l1
    i32.const 16
    i32.add
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h73fad27a55c2a023E
    local.get $p0
    call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E
    call $_ZN17soroban_env_guest5guest7context14contract_event17ha9a5af34bd21bbfcE
    drop
    local.get $l1
    i32.const 96
    i32.add
    global.set $__stack_pointer
    i64.const 2)
  (func $get_subscription (type $t2) (param $p0 i64) (result i64)
    (local $l1 i32)
    global.get $__stack_pointer
    i32.const 176
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    local.get $p0
    call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E
    block  ;; label = @1
      block  ;; label = @2
        local.get $l1
        i64.load
        i32.wrap_i64
        br_if 0 (;@2;)
        local.get $l1
        i64.load offset=8
        local.set $p0
        call $_ZN23reflector_subscriptions24panic_if_not_initialized17h9f5369fdfb879af3E
        local.get $l1
        i32.const 96
        i32.add
        local.get $p0
        call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$16get_subscription17hcc54efa06af29242E
        local.get $l1
        i32.load8_u offset=168
        i32.const 2
        i32.ne
        br_if 1 (;@1;)
        i64.const 8589934595
        call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
      end
      unreachable
      unreachable
    end
    local.get $l1
    i32.const 16
    i32.add
    local.get $l1
    i32.const 96
    i32.add
    i32.const 80
    call $memcpy
    drop
    local.get $l1
    i32.const 16
    i32.add
    call $_ZN23reflector_subscriptions5types12subscription188_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$reflector_subscriptions..types..subscription..Subscription$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17hb05340ab0a18289cE
    local.set $p0
    local.get $l1
    i32.const 176
    i32.add
    global.set $__stack_pointer
    local.get $p0)
  (func $get_retention_fee (type $t2) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i32) (local $l3 i64)
    global.get $__stack_pointer
    i32.const 96
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    local.get $p0
    call $_ZN103_$LT$u64$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h345e3d11271c9748E
    block  ;; label = @1
      block  ;; label = @2
        local.get $l1
        i64.load
        i32.wrap_i64
        br_if 0 (;@2;)
        local.get $l1
        i64.load offset=8
        local.set $p0
        call $_ZN23reflector_subscriptions24panic_if_not_initialized17h9f5369fdfb879af3E
        local.get $l1
        i32.const 16
        i32.add
        local.get $p0
        call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$16get_subscription17hcc54efa06af29242E
        local.get $l1
        i32.load8_u offset=88
        i32.const 2
        i32.ne
        br_if 1 (;@1;)
        i64.const 8589934595
        call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$15fail_with_error17h921998c0d4b32106E
      end
      unreachable
      unreachable
    end
    local.get $l1
    i32.load offset=84
    local.set $l2
    local.get $l1
    i64.load offset=48
    local.set $p0
    local.get $l1
    i64.load offset=32
    local.set $l3
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$7get_fee17h2069b1bb14de6c5eE
    local.get $l3
    local.get $p0
    local.get $l2
    call $_ZN23reflector_subscriptions8calc_fee17h9c62d7e4ca088a5fE
    call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E
    local.set $p0
    local.get $l1
    i32.const 96
    i32.add
    global.set $__stack_pointer
    local.get $p0)
  (func $last_id (type $t6) (result i64)
    call $_ZN23reflector_subscriptions24panic_if_not_initialized17h9f5369fdfb879af3E
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$24get_last_subscription_id17h1afdcc0bc6309984E
    call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E)
  (func $admin (type $t6) (result i64)
    (local $l0 i32) (local $l1 i64) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$9get_admin17he97dcfa05af55c08E
    local.get $l0
    i64.load
    local.set $l1
    local.get $l0
    i64.load offset=8
    local.set $l2
    local.get $l0
    i32.const 16
    i32.add
    global.set $__stack_pointer
    i64.const 2
    local.get $l2
    local.get $l1
    i64.eqz
    select)
  (func $version (type $t6) (result i64)
    (local $l0 i32) (local $l1 i32) (local $l2 i32) (local $l3 i32) (local $l4 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    i32.const 0
    local.set $l1
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          loop  ;; label = @4
            block  ;; label = @5
              local.get $l1
              local.tee $l2
              i32.const 4
              i32.le_u
              br_if 0 (;@5;)
              i32.const 5
              local.set $l2
              br 2 (;@3;)
            end
            local.get $l2
            i32.const 1
            i32.add
            local.set $l1
            local.get $l2
            i32.const 1048912
            i32.add
            i32.load8_u
            i32.const 63
            i32.and
            i32.const 46
            i32.ne
            br_if 0 (;@4;)
            i32.const -1
            local.set $l1
            block  ;; label = @5
              loop  ;; label = @6
                local.get $l1
                i32.eqz
                br_if 1 (;@5;)
                local.get $l2
                local.get $l1
                i32.add
                local.tee $l3
                i32.const 4
                i32.eq
                br_if 4 (;@2;)
                local.get $l1
                i32.const 1
                i32.add
                local.set $l1
                local.get $l3
                i32.const 1048913
                i32.add
                i32.load8_u
                i32.const 46
                i32.eq
                br_if 0 (;@6;)
              end
              local.get $l2
              local.get $l1
              i32.add
              i32.const 1
              i32.add
              local.set $l1
              br 1 (;@4;)
            end
          end
          local.get $l2
          i32.eqz
          br_if 2 (;@1;)
        end
        i32.const 0
        local.set $l1
        local.get $l2
        i32.const 1
        i32.ne
        local.set $l4
        i32.const 0
        local.set $l3
        loop  ;; label = @3
          local.get $l4
          br_if 2 (;@1;)
          local.get $l1
          i32.const 1048912
          i32.add
          i32.load8_u
          local.get $l3
          i32.const 10
          i32.mul
          i32.add
          i32.const -48
          i32.add
          local.set $l3
          local.get $l2
          local.get $l1
          i32.const 1
          i32.add
          local.tee $l1
          i32.ne
          br_if 0 (;@3;)
        end
        local.get $l0
        i32.const 16
        i32.add
        global.set $__stack_pointer
        local.get $l3
        i64.extend_i32_u
        i64.const 32
        i64.shl
        i64.const 4
        i64.or
        return
      end
      local.get $l2
      i32.const 5
      local.get $l2
      i32.const 5
      i32.gt_u
      select
      i32.const 5
      call $_ZN4core9panicking18panic_bounds_check17hc47765e3d10a3709E
      unreachable
    end
    i32.const 1049568
    local.get $l0
    i32.const 15
    i32.add
    i32.const 1048576
    call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
    unreachable)
  (func $_ZN4core9panicking18panic_bounds_check17hc47765e3d10a3709E (type $t26) (param $p0 i32) (param $p1 i32)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $fee (type $t6) (result i64)
    call $_ZN23reflector_subscriptions24panic_if_not_initialized17h9f5369fdfb879af3E
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$7get_fee17h2069b1bb14de6c5eE
    call $_ZN103_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$u64$GT$$GT$12try_from_val17h60af93a298f03e91E)
  (func $token (type $t6) (result i64)
    call $_ZN23reflector_subscriptions24panic_if_not_initialized17h9f5369fdfb879af3E
    call $_ZN108_$LT$soroban_sdk..env..Env$u20$as$u20$reflector_subscriptions..extensions..env_extensions..EnvExtensions$GT$9get_token17hb38f055530f2a96eE)
  (func $_ZN4core3fmt3num3imp7fmt_u6417hdb0013e0ceafa0e4E (type $t27) (param $p0 i64) (param $p1 i32) (param $p2 i32) (result i32)
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
        i64.const 10000
        i64.div_u
        local.tee $l5
        i64.const 55536
        i64.mul
        local.get $p0
        i64.add
        i32.wrap_i64
        local.tee $l7
        i32.const 65535
        i32.and
        i32.const 100
        i32.div_u
        local.tee $l8
        i32.const 1
        i32.shl
        i32.const 1049047
        i32.add
        i32.load16_u align=1
        i32.store16 align=1
        local.get $l6
        i32.const -2
        i32.add
        local.get $l8
        i32.const -100
        i32.mul
        local.get $l7
        i32.add
        i32.const 65535
        i32.and
        i32.const 1
        i32.shl
        i32.const 1049047
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
      local.tee $l7
      i32.const 65535
      i32.and
      i32.const 100
      i32.div_u
      local.tee $l6
      i32.const -100
      i32.mul
      local.get $l7
      i32.add
      i32.const 65535
      i32.and
      i32.const 1
      i32.shl
      i32.const 1049047
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
        i32.const 1049047
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
  (func $_ZN4core3fmt9Formatter12pad_integral17h7dae91fc148a1aefE (type $t28) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (param $p4 i32) (param $p5 i32) (result i32)
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
          br_if 0 (;@3;)
          i32.const 0
          local.set $l9
          br 1 (;@2;)
        end
        block  ;; label = @3
          local.get $p3
          i32.const 3
          i32.and
          local.tee $l10
          br_if 0 (;@3;)
          br 1 (;@2;)
        end
        i32.const 0
        local.set $l9
        local.get $p2
        local.set $p1
        loop  ;; label = @3
          local.get $l9
          local.get $p1
          i32.load8_s
          i32.const -65
          i32.gt_s
          i32.add
          local.set $l9
          local.get $p1
          i32.const 1
          i32.add
          local.set $p1
          local.get $l10
          i32.const -1
          i32.add
          local.tee $l10
          br_if 0 (;@3;)
        end
      end
      local.get $l9
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
        local.tee $l9
        local.get $p0
        i32.load offset=24
        local.tee $l10
        local.get $l8
        local.get $p2
        local.get $p3
        call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
        br_if 1 (;@1;)
        local.get $l9
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
        local.tee $l11
        local.get $l6
        i32.gt_u
        br_if 0 (;@2;)
        i32.const 1
        local.set $p1
        local.get $p0
        i32.load offset=20
        local.tee $l9
        local.get $p0
        i32.load offset=24
        local.tee $l10
        local.get $l8
        local.get $p2
        local.get $p3
        call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
        br_if 1 (;@1;)
        local.get $l9
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
        local.set $l7
        local.get $p0
        i32.const 48
        i32.store offset=16
        local.get $p0
        i32.load8_u offset=32
        local.set $l12
        i32.const 1
        local.set $p1
        local.get $p0
        i32.const 1
        i32.store8 offset=32
        local.get $p0
        i32.load offset=20
        local.tee $l9
        local.get $p0
        i32.load offset=24
        local.tee $l10
        local.get $l8
        local.get $p2
        local.get $p3
        call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
        br_if 1 (;@1;)
        local.get $l11
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
            local.get $l9
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
        local.get $l9
        local.get $p4
        local.get $p5
        local.get $l10
        i32.load offset=12
        call_indirect $T0 (type $t0)
        br_if 1 (;@1;)
        local.get $p0
        local.get $l12
        i32.store8 offset=32
        local.get $p0
        local.get $l7
        i32.store offset=16
        i32.const 0
        local.set $p1
        br 1 (;@1;)
      end
      local.get $l11
      local.get $l6
      i32.sub
      local.set $l7
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            local.get $p0
            i32.load8_u offset=32
            local.tee $p1
            br_table 2 (;@2;) 0 (;@4;) 1 (;@3;) 0 (;@4;) 2 (;@2;)
          end
          local.get $l7
          local.set $p1
          i32.const 0
          local.set $l7
          br 1 (;@2;)
        end
        local.get $l7
        i32.const 1
        i32.shr_u
        local.set $p1
        local.get $l7
        i32.const 1
        i32.add
        i32.const 1
        i32.shr_u
        local.set $l7
      end
      local.get $p1
      i32.const 1
      i32.add
      local.set $p1
      local.get $p0
      i32.load offset=16
      local.set $l6
      local.get $p0
      i32.load offset=24
      local.set $l9
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
          local.get $l6
          local.get $l9
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
      local.get $l9
      local.get $l8
      local.get $p2
      local.get $p3
      call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
      br_if 0 (;@1;)
      local.get $l10
      local.get $p4
      local.get $p5
      local.get $l9
      i32.load offset=12
      call_indirect $T0 (type $t0)
      br_if 0 (;@1;)
      i32.const 0
      local.set $p1
      loop  ;; label = @2
        block  ;; label = @3
          local.get $l7
          local.get $p1
          i32.ne
          br_if 0 (;@3;)
          local.get $l7
          local.get $l7
          i32.lt_u
          return
        end
        local.get $p1
        i32.const 1
        i32.add
        local.set $p1
        local.get $l10
        local.get $l6
        local.get $l9
        i32.load offset=16
        call_indirect $T0 (type $t1)
        i32.eqz
        br_if 0 (;@2;)
      end
      local.get $p1
      i32.const -1
      i32.add
      local.get $l7
      i32.lt_u
      return
    end
    local.get $p1)
  (func $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E (type $t29) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (param $p4 i32) (result i32)
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
  (func $_ZN4core3fmt9Formatter3pad17hdad3e25ba05328b0E (type $t0) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32) (local $l7 i32) (local $l8 i32) (local $l9 i32) (local $l10 i32) (local $l11 i32) (local $l12 i32) (local $l13 i32)
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p0
          i32.load
          local.tee $l3
          local.get $p0
          i32.load offset=8
          local.tee $l4
          i32.or
          i32.eqz
          br_if 0 (;@3;)
          block  ;; label = @4
            local.get $l4
            i32.eqz
            br_if 0 (;@4;)
            local.get $p1
            local.get $p2
            i32.add
            local.set $l5
            block  ;; label = @5
              block  ;; label = @6
                local.get $p0
                i32.load offset=12
                local.tee $l6
                br_if 0 (;@6;)
                i32.const 0
                local.set $l7
                local.get $p1
                local.set $l8
                br 1 (;@5;)
              end
              i32.const 0
              local.set $l7
              i32.const 0
              local.set $l9
              local.get $p1
              local.set $l8
              loop  ;; label = @6
                local.get $l8
                local.tee $l4
                local.get $l5
                i32.eq
                br_if 2 (;@4;)
                block  ;; label = @7
                  block  ;; label = @8
                    local.get $l4
                    i32.load8_s
                    local.tee $l8
                    i32.const -1
                    i32.le_s
                    br_if 0 (;@8;)
                    local.get $l4
                    i32.const 1
                    i32.add
                    local.set $l8
                    br 1 (;@7;)
                  end
                  block  ;; label = @8
                    local.get $l8
                    i32.const -32
                    i32.ge_u
                    br_if 0 (;@8;)
                    local.get $l4
                    i32.const 2
                    i32.add
                    local.set $l8
                    br 1 (;@7;)
                  end
                  block  ;; label = @8
                    local.get $l8
                    i32.const -16
                    i32.ge_u
                    br_if 0 (;@8;)
                    local.get $l4
                    i32.const 3
                    i32.add
                    local.set $l8
                    br 1 (;@7;)
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
                local.get $l9
                i32.const 1
                i32.add
                local.tee $l9
                i32.ne
                br_if 0 (;@6;)
              end
            end
            local.get $l8
            local.get $l5
            i32.eq
            br_if 0 (;@4;)
            block  ;; label = @5
              local.get $l8
              i32.load8_s
              local.tee $l4
              i32.const -1
              i32.gt_s
              br_if 0 (;@5;)
              local.get $l4
              i32.const -32
              i32.lt_u
              drop
            end
            block  ;; label = @5
              block  ;; label = @6
                local.get $l7
                i32.eqz
                br_if 0 (;@6;)
                block  ;; label = @7
                  local.get $l7
                  local.get $p2
                  i32.ge_u
                  br_if 0 (;@7;)
                  i32.const 0
                  local.set $l4
                  local.get $p1
                  local.get $l7
                  i32.add
                  i32.load8_s
                  i32.const -65
                  i32.gt_s
                  br_if 1 (;@6;)
                  br 2 (;@5;)
                end
                i32.const 0
                local.set $l4
                local.get $l7
                local.get $p2
                i32.ne
                br_if 1 (;@5;)
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
          block  ;; label = @4
            local.get $l3
            br_if 0 (;@4;)
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
          local.set $l10
          block  ;; label = @4
            local.get $p2
            i32.const 16
            i32.lt_u
            br_if 0 (;@4;)
            local.get $p2
            local.get $p1
            local.get $p1
            i32.const 3
            i32.add
            i32.const -4
            i32.and
            local.tee $l7
            i32.sub
            local.tee $l9
            i32.add
            local.tee $l11
            i32.const 3
            i32.and
            local.set $l3
            i32.const 0
            local.set $l6
            i32.const 0
            local.set $l4
            block  ;; label = @5
              local.get $p1
              local.get $l7
              i32.eq
              br_if 0 (;@5;)
              i32.const 0
              local.set $l4
              block  ;; label = @6
                local.get $l9
                i32.const -4
                i32.gt_u
                br_if 0 (;@6;)
                i32.const 0
                local.set $l4
                i32.const 0
                local.set $l5
                loop  ;; label = @7
                  local.get $l4
                  local.get $p1
                  local.get $l5
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
                  i32.const 4
                  i32.add
                  local.tee $l5
                  br_if 0 (;@7;)
                end
              end
              local.get $p1
              local.set $l8
              loop  ;; label = @6
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
                local.get $l9
                i32.const 1
                i32.add
                local.tee $l9
                br_if 0 (;@6;)
              end
            end
            block  ;; label = @5
              local.get $l3
              i32.eqz
              br_if 0 (;@5;)
              local.get $l7
              local.get $l11
              i32.const -4
              i32.and
              i32.add
              local.tee $l8
              i32.load8_s
              i32.const -65
              i32.gt_s
              local.set $l6
              local.get $l3
              i32.const 1
              i32.eq
              br_if 0 (;@5;)
              local.get $l6
              local.get $l8
              i32.load8_s offset=1
              i32.const -65
              i32.gt_s
              i32.add
              local.set $l6
              local.get $l3
              i32.const 2
              i32.eq
              br_if 0 (;@5;)
              local.get $l6
              local.get $l8
              i32.load8_s offset=2
              i32.const -65
              i32.gt_s
              i32.add
              local.set $l6
            end
            local.get $l11
            i32.const 2
            i32.shr_u
            local.set $l5
            local.get $l6
            local.get $l4
            i32.add
            local.set $l6
            loop  ;; label = @5
              local.get $l7
              local.set $l3
              local.get $l5
              i32.eqz
              br_if 4 (;@1;)
              local.get $l5
              i32.const 192
              local.get $l5
              i32.const 192
              i32.lt_u
              select
              local.tee $l11
              i32.const 3
              i32.and
              local.set $l12
              local.get $l11
              i32.const 2
              i32.shl
              local.set $l13
              i32.const 0
              local.set $l8
              block  ;; label = @6
                local.get $l5
                i32.const 4
                i32.lt_u
                br_if 0 (;@6;)
                local.get $l3
                local.get $l13
                i32.const 1008
                i32.and
                i32.add
                local.set $l9
                i32.const 0
                local.set $l8
                local.get $l3
                local.set $l4
                loop  ;; label = @7
                  local.get $l4
                  i32.load offset=12
                  local.tee $l7
                  i32.const -1
                  i32.xor
                  i32.const 7
                  i32.shr_u
                  local.get $l7
                  i32.const 6
                  i32.shr_u
                  i32.or
                  i32.const 16843009
                  i32.and
                  local.get $l4
                  i32.load offset=8
                  local.tee $l7
                  i32.const -1
                  i32.xor
                  i32.const 7
                  i32.shr_u
                  local.get $l7
                  i32.const 6
                  i32.shr_u
                  i32.or
                  i32.const 16843009
                  i32.and
                  local.get $l4
                  i32.load offset=4
                  local.tee $l7
                  i32.const -1
                  i32.xor
                  i32.const 7
                  i32.shr_u
                  local.get $l7
                  i32.const 6
                  i32.shr_u
                  i32.or
                  i32.const 16843009
                  i32.and
                  local.get $l4
                  i32.load
                  local.tee $l7
                  i32.const -1
                  i32.xor
                  i32.const 7
                  i32.shr_u
                  local.get $l7
                  i32.const 6
                  i32.shr_u
                  i32.or
                  i32.const 16843009
                  i32.and
                  local.get $l8
                  i32.add
                  i32.add
                  i32.add
                  i32.add
                  local.set $l8
                  local.get $l4
                  i32.const 16
                  i32.add
                  local.tee $l4
                  local.get $l9
                  i32.ne
                  br_if 0 (;@7;)
                end
              end
              local.get $l5
              local.get $l11
              i32.sub
              local.set $l5
              local.get $l3
              local.get $l13
              i32.add
              local.set $l7
              local.get $l8
              i32.const 8
              i32.shr_u
              i32.const 16711935
              i32.and
              local.get $l8
              i32.const 16711935
              i32.and
              i32.add
              i32.const 65537
              i32.mul
              i32.const 16
              i32.shr_u
              local.get $l6
              i32.add
              local.set $l6
              local.get $l12
              i32.eqz
              br_if 0 (;@5;)
            end
            local.get $l3
            local.get $l11
            i32.const 252
            i32.and
            i32.const 2
            i32.shl
            i32.add
            local.tee $l8
            i32.load
            local.tee $l4
            i32.const -1
            i32.xor
            i32.const 7
            i32.shr_u
            local.get $l4
            i32.const 6
            i32.shr_u
            i32.or
            i32.const 16843009
            i32.and
            local.set $l4
            local.get $l12
            i32.const 1
            i32.eq
            br_if 2 (;@2;)
            local.get $l8
            i32.load offset=4
            local.tee $l7
            i32.const -1
            i32.xor
            i32.const 7
            i32.shr_u
            local.get $l7
            i32.const 6
            i32.shr_u
            i32.or
            i32.const 16843009
            i32.and
            local.get $l4
            i32.add
            local.set $l4
            local.get $l12
            i32.const 2
            i32.eq
            br_if 2 (;@2;)
            local.get $l8
            i32.load offset=8
            local.tee $l8
            i32.const -1
            i32.xor
            i32.const 7
            i32.shr_u
            local.get $l8
            i32.const 6
            i32.shr_u
            i32.or
            i32.const 16843009
            i32.and
            local.get $l4
            i32.add
            local.set $l4
            br 2 (;@2;)
          end
          block  ;; label = @4
            local.get $p2
            br_if 0 (;@4;)
            i32.const 0
            local.set $l6
            br 3 (;@1;)
          end
          local.get $p2
          i32.const 3
          i32.and
          local.set $l8
          block  ;; label = @4
            block  ;; label = @5
              local.get $p2
              i32.const 4
              i32.ge_u
              br_if 0 (;@5;)
              i32.const 0
              local.set $l6
              i32.const 0
              local.set $l9
              br 1 (;@4;)
            end
            i32.const 0
            local.set $l6
            local.get $p1
            local.set $l4
            local.get $p2
            i32.const 12
            i32.and
            local.tee $l9
            local.set $l7
            loop  ;; label = @5
              local.get $l6
              local.get $l4
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.get $l4
              i32.const 1
              i32.add
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.get $l4
              i32.const 2
              i32.add
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.get $l4
              i32.const 3
              i32.add
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.set $l6
              local.get $l4
              i32.const 4
              i32.add
              local.set $l4
              local.get $l7
              i32.const -4
              i32.add
              local.tee $l7
              br_if 0 (;@5;)
            end
          end
          local.get $l8
          i32.eqz
          br_if 2 (;@1;)
          local.get $p1
          local.get $l9
          i32.add
          local.set $l4
          loop  ;; label = @4
            local.get $l6
            local.get $l4
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.set $l6
            local.get $l4
            i32.const 1
            i32.add
            local.set $l4
            local.get $l8
            i32.const -1
            i32.add
            local.tee $l8
            br_if 0 (;@4;)
            br 3 (;@1;)
          end
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
      local.get $l4
      i32.const 8
      i32.shr_u
      i32.const 459007
      i32.and
      local.get $l4
      i32.const 16711935
      i32.and
      i32.add
      i32.const 65537
      i32.mul
      i32.const 16
      i32.shr_u
      local.get $l6
      i32.add
      local.set $l6
    end
    block  ;; label = @1
      block  ;; label = @2
        local.get $l10
        local.get $l6
        i32.le_u
        br_if 0 (;@2;)
        local.get $l10
        local.get $l6
        i32.sub
        local.set $l5
        i32.const 0
        local.set $l4
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              local.get $p0
              i32.load8_u offset=32
              br_table 2 (;@3;) 0 (;@5;) 1 (;@4;) 2 (;@3;) 2 (;@3;)
            end
            local.get $l5
            local.set $l4
            i32.const 0
            local.set $l5
            br 1 (;@3;)
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
        local.set $l9
        local.get $p0
        i32.load offset=24
        local.set $l8
        local.get $p0
        i32.load offset=20
        local.set $l7
        loop  ;; label = @3
          local.get $l4
          i32.const -1
          i32.add
          local.tee $l4
          i32.eqz
          br_if 2 (;@1;)
          local.get $l7
          local.get $l9
          local.get $l8
          i32.load offset=16
          call_indirect $T0 (type $t1)
          i32.eqz
          br_if 0 (;@3;)
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
    block  ;; label = @1
      local.get $l7
      local.get $p1
      local.get $p2
      local.get $l8
      i32.load offset=12
      call_indirect $T0 (type $t0)
      br_if 0 (;@1;)
      i32.const 0
      local.set $l4
      block  ;; label = @2
        loop  ;; label = @3
          block  ;; label = @4
            local.get $l5
            local.get $l4
            i32.ne
            br_if 0 (;@4;)
            local.get $l5
            local.set $l4
            br 2 (;@2;)
          end
          local.get $l4
          i32.const 1
          i32.add
          local.set $l4
          local.get $l7
          local.get $l9
          local.get $l8
          i32.load offset=16
          call_indirect $T0 (type $t1)
          i32.eqz
          br_if 0 (;@3;)
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
    local.get $l4)
  (func $_ZN4core9panicking5panic17hcaca2598a27ec0fcE (type $t26) (param $p0 i32) (param $p1 i32)
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
  (func $_ZN68_$LT$core..fmt..builders..PadAdapter$u20$as$u20$core..fmt..Write$GT$10write_char17hdff090ddce8dafe2E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32) (local $l3 i32)
    local.get $p0
    i32.load offset=4
    local.set $l2
    local.get $p0
    i32.load
    local.set $l3
    block  ;; label = @1
      local.get $p0
      i32.load offset=8
      local.tee $p0
      i32.load8_u
      i32.eqz
      br_if 0 (;@1;)
      local.get $l3
      i32.const 1049032
      i32.const 4
      local.get $l2
      i32.load offset=12
      call_indirect $T0 (type $t0)
      i32.eqz
      br_if 0 (;@1;)
      i32.const 1
      return
    end
    local.get $p0
    local.get $p1
    i32.const 10
    i32.eq
    i32.store8
    local.get $l3
    local.get $p1
    local.get $l2
    i32.load offset=16
    call_indirect $T0 (type $t1))
  (func $_ZN4core3fmt5Write9write_fmt17h07171b83fe780f81E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p0
    i32.const 1049008
    local.get $p1
    call $_ZN4core3fmt5write17hbbcd4b328f92d3c5E)
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
  (func $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17ha809c79264ce9df7E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p1
    local.get $p0
    i32.load
    local.get $p0
    i32.load offset=4
    call $_ZN4core3fmt9Formatter3pad17hdad3e25ba05328b0E)
  (func $_ZN69_$LT$soroban_env_common..error..Error$u20$as$u20$core..fmt..Debug$GT$3fmt17hd585753a7f4f1074E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32) (local $l3 i64) (local $l4 i32) (local $l5 i32)
    global.get $__stack_pointer
    i32.const 96
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
    i32.store offset=32
    local.get $l2
    local.get $l3
    i64.const 32
    i64.shr_u
    i32.wrap_i64
    local.tee $l5
    i32.store offset=36
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            local.get $p0
            i32.const 2559
            i32.gt_u
            br_if 0 (;@4;)
            local.get $p0
            i32.const 256
            i32.lt_u
            br_if 1 (;@3;)
            local.get $l2
            i32.const 16
            i32.add
            local.get $l4
            call $_ZN11stellar_xdr4curr9generated11ScErrorType4name17hbf0cb27a2916401bE
            local.get $l2
            i32.load offset=20
            local.set $p0
            local.get $l2
            i32.load offset=16
            local.set $l4
            block  ;; label = @5
              local.get $l5
              i32.const 10
              i32.ge_u
              br_if 0 (;@5;)
              local.get $l2
              local.get $p0
              i32.store offset=44
              local.get $l2
              local.get $l4
              i32.store offset=40
              local.get $l2
              i32.const 8
              i32.add
              local.get $l5
              call $_ZN11stellar_xdr4curr9generated11ScErrorCode4name17hd2f62f5688ef6d0dE
              local.get $l2
              i32.const 92
              i32.add
              i32.const 1
              i32.store
              local.get $l2
              i32.const 1
              i32.store offset=84
              local.get $l2
              i32.const 3
              i32.store offset=60
              local.get $l2
              i32.const 1049444
              i32.store offset=56
              local.get $l2
              i64.const 2
              i64.store offset=68 align=4
              local.get $l2
              local.get $l2
              i64.load offset=8
              i64.store offset=48 align=4
              local.get $l2
              local.get $l2
              i32.const 48
              i32.add
              i32.store offset=88
              local.get $l2
              local.get $l2
              i32.const 40
              i32.add
              i32.store offset=80
              local.get $l2
              local.get $l2
              i32.const 80
              i32.add
              i32.store offset=64
              local.get $p1
              i32.load offset=20
              local.get $p1
              i32.load offset=24
              local.get $l2
              i32.const 56
              i32.add
              call $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE
              local.set $p1
              br 4 (;@1;)
            end
            local.get $l2
            i32.const 92
            i32.add
            i32.const 2
            i32.store
            local.get $l2
            i32.const 3
            i32.store offset=60
            local.get $l2
            i32.const 1049472
            i32.store offset=56
            local.get $l2
            i64.const 2
            i64.store offset=68 align=4
            local.get $l2
            i32.const 1
            i32.store offset=84
            local.get $l2
            local.get $p0
            i32.store offset=52
            local.get $l2
            local.get $l4
            i32.store offset=48
            local.get $l2
            local.get $l2
            i32.const 80
            i32.add
            i32.store offset=64
            local.get $l2
            local.get $l2
            i32.const 36
            i32.add
            i32.store offset=88
            local.get $l2
            local.get $l2
            i32.const 48
            i32.add
            i32.store offset=80
            local.get $p1
            i32.load offset=20
            local.get $p1
            i32.load offset=24
            local.get $l2
            i32.const 56
            i32.add
            call $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE
            local.set $p1
            br 3 (;@1;)
          end
          local.get $l5
          i32.const 10
          i32.lt_u
          br_if 1 (;@2;)
          local.get $l2
          i32.const 92
          i32.add
          i32.const 2
          i32.store
          local.get $l2
          i32.const 3
          i32.store offset=60
          local.get $l2
          i32.const 1049528
          i32.store offset=56
          local.get $l2
          i64.const 2
          i64.store offset=68 align=4
          local.get $l2
          i32.const 2
          i32.store offset=84
          local.get $l2
          local.get $l2
          i32.const 80
          i32.add
          i32.store offset=64
          local.get $l2
          local.get $l2
          i32.const 36
          i32.add
          i32.store offset=88
          local.get $l2
          local.get $l2
          i32.const 32
          i32.add
          i32.store offset=80
          local.get $p1
          i32.load offset=20
          local.get $p1
          i32.load offset=24
          local.get $l2
          i32.const 56
          i32.add
          call $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE
          local.set $p1
          br 2 (;@1;)
        end
        local.get $l2
        local.get $l4
        call $_ZN11stellar_xdr4curr9generated11ScErrorType4name17hbf0cb27a2916401bE
        local.get $l2
        i32.const 92
        i32.add
        i32.const 2
        i32.store
        local.get $l2
        i32.const 1
        i32.store offset=84
        local.get $l2
        i32.const 3
        i32.store offset=60
        local.get $l2
        i32.const 1049472
        i32.store offset=56
        local.get $l2
        i64.const 2
        i64.store offset=68 align=4
        local.get $l2
        local.get $l2
        i64.load
        i64.store offset=48 align=4
        local.get $l2
        local.get $l2
        i32.const 36
        i32.add
        i32.store offset=88
        local.get $l2
        local.get $l2
        i32.const 48
        i32.add
        i32.store offset=80
        local.get $l2
        local.get $l2
        i32.const 80
        i32.add
        i32.store offset=64
        local.get $p1
        i32.load offset=20
        local.get $p1
        i32.load offset=24
        local.get $l2
        i32.const 56
        i32.add
        call $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE
        local.set $p1
        br 1 (;@1;)
      end
      local.get $l2
      i32.const 24
      i32.add
      local.get $l5
      call $_ZN11stellar_xdr4curr9generated11ScErrorCode4name17hd2f62f5688ef6d0dE
      local.get $l2
      i32.const 92
      i32.add
      i32.const 1
      i32.store
      local.get $l2
      i32.const 2
      i32.store offset=84
      local.get $l2
      i32.const 3
      i32.store offset=60
      local.get $l2
      i32.const 1049504
      i32.store offset=56
      local.get $l2
      i64.const 2
      i64.store offset=68 align=4
      local.get $l2
      local.get $l2
      i64.load offset=24
      i64.store offset=48 align=4
      local.get $l2
      local.get $l2
      i32.const 48
      i32.add
      i32.store offset=88
      local.get $l2
      local.get $l2
      i32.const 32
      i32.add
      i32.store offset=80
      local.get $l2
      local.get $l2
      i32.const 80
      i32.add
      i32.store offset=64
      local.get $p1
      i32.load offset=20
      local.get $p1
      i32.load offset=24
      local.get $l2
      i32.const 56
      i32.add
      call $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE
      local.set $p1
    end
    local.get $l2
    i32.const 96
    i32.add
    global.set $__stack_pointer
    local.get $p1)
  (func $_ZN11stellar_xdr4curr9generated11ScErrorType4name17hbf0cb27a2916401bE (type $t26) (param $p0 i32) (param $p1 i32)
    local.get $p0
    local.get $p1
    i32.const 2
    i32.shl
    local.tee $p1
    i32.const 1049644
    i32.add
    i32.load
    i32.store offset=4
    local.get $p0
    local.get $p1
    i32.const 1049684
    i32.add
    i32.load
    i32.store)
  (func $_ZN11stellar_xdr4curr9generated11ScErrorCode4name17hd2f62f5688ef6d0dE (type $t26) (param $p0 i32) (param $p1 i32)
    local.get $p0
    local.get $p1
    i32.const 2
    i32.shl
    local.tee $p1
    i32.const 1049724
    i32.add
    i32.load
    i32.store offset=4
    local.get $p0
    local.get $p1
    i32.const 1049764
    i32.add
    i32.load
    i32.store)
  (func $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE (type $t0) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    block  ;; label = @1
      local.get $p2
      i32.load offset=4
      br_table 0 (;@1;) 0 (;@1;) 0 (;@1;)
    end
    local.get $p0
    local.get $p1
    local.get $p2
    call $_ZN4core3fmt5write17hbbcd4b328f92d3c5E)
  (func $_ (type $t18))
  (func $_ZN77_$LT$soroban_env_common..val..ConversionError$u20$as$u20$core..fmt..Debug$GT$3fmt17hc11bf815ae7c9784E.82 (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p1
    i32.load offset=20
    i32.const 1049628
    i32.const 15
    local.get $p1
    i32.load offset=24
    i32.load offset=12
    call_indirect $T0 (type $t0))
  (func $__ashlti3 (type $t30) (param $p0 i32) (param $p1 i64) (param $p2 i64) (param $p3 i32)
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
  (func $__multi3 (type $t31) (param $p0 i32) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64)
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
  (func $_ZN17compiler_builtins3int19specialized_div_rem12u128_div_rem17h037f7f51afb6bf78E (type $t31) (param $p0 i32) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64)
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
  (func $__udivti3 (type $t31) (param $p0 i32) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64)
    (local $l5 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l5
    global.set $__stack_pointer
    local.get $l5
    local.get $p1
    local.get $p2
    local.get $p3
    local.get $p4
    call $_ZN17compiler_builtins3int19specialized_div_rem12u128_div_rem17h037f7f51afb6bf78E
    local.get $l5
    i64.load
    local.set $p4
    local.get $p0
    local.get $l5
    i32.const 8
    i32.add
    i64.load
    i64.store offset=8
    local.get $p0
    local.get $p4
    i64.store
    local.get $l5
    i32.const 32
    i32.add
    global.set $__stack_pointer)
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
  (table $T0 9 9 funcref)
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1049804))
  (global $__heap_base i32 (i32.const 1049808))
  (export "memory" (memory $memory))
  (export "sunbeam_entrypt" (func $sunbeam_entrypt))
  (export "config" (func $config))
  (export "set_fee" (func $set_fee))
  (export "trigger" (func $trigger))
  (export "charge" (func $charge))
  (export "update_contract" (func $update_contract))
  (export "create_subscription" (func $create_subscription))
  (export "deposit" (func $deposit))
  (export "cancel" (func $cancel))
  (export "get_subscription" (func $get_subscription))
  (export "get_retention_fee" (func $get_retention_fee))
  (export "last_id" (func $last_id))
  (export "admin" (func $admin))
  (export "version" (func $version))
  (export "fee" (func $fee))
  (export "token" (func $token))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (elem $e0 (i32.const 1) func $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17ha809c79264ce9df7E $_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i32$GT$3fmt17hd6308d8453dcc3baE $_ZN68_$LT$core..num..error..ParseIntError$u20$as$u20$core..fmt..Debug$GT$3fmt17h8f58b2f81c940f7dE $_ZN68_$LT$core..fmt..builders..PadAdapter$u20$as$u20$core..fmt..Write$GT$9write_str17hf46b591acfd1be0dE $_ZN68_$LT$core..fmt..builders..PadAdapter$u20$as$u20$core..fmt..Write$GT$10write_char17hdff090ddce8dafe2E $_ZN4core3fmt5Write9write_fmt17h07171b83fe780f81E $_ZN77_$LT$soroban_env_common..val..ConversionError$u20$as$u20$core..fmt..Debug$GT$3fmt17hc11bf815ae7c9784E.82 $_ZN69_$LT$soroban_env_common..error..Error$u20$as$u20$core..fmt..Debug$GT$3fmt17hd585753a7f4f1074E)
  (data $.rodata (i32.const 1048576) "\00\00\00\00\01\00\00\00\01\00\00\00\03\00\00\00EmptyInvalidDigitPosOverflowNegOverflowZeroParseIntErrorkindadminbase_feetokenlastassetsource\00\00\00b\00\10\00\05\00\00\00g\00\10\00\06\00\00\00balancebaseheartbeatownerquotestatusthresholdupdatedwebhook\00\80\00\10\00\07\00\00\00\87\00\10\00\04\00\00\00\8b\00\10\00\09\00\00\00\94\00\10\00\05\00\00\00\99\00\10\00\05\00\00\00\9e\00\10\00\06\00\00\00\a4\00\10\00\09\00\00\00\ad\00\10\00\07\00\00\00\b4\00\10\00\07\00\00\00fee\00L\00\10\00\05\00\00\00\04\01\10\00\03\00\00\00Y\00\10\00\05\00\00\00\87\00\10\00\04\00\00\00\8b\00\10\00\09\00\00\00\94\00\10\00\05\00\00\00\99\00\10\00\05\00\00\00\a4\00\10\00\09\00\00\00\b4\00\10\00\07\00\00\001.0.0\00\00\00\05\00\00\00\0c\00\00\00\0b\00\00\00\0b\00\00\00\04\00\00\00\10\00\10\00\15\00\10\00!\00\10\00,\00\10\007\00\10\00called `Option::unwrap()` on a `None` value: \00\00\00\00\00\00\00\0c\00\00\00\04\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00     {  {\0a,\0a} }00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899ArithDomainIndexBoundsInvalidInputMissingValueExistingValueExceededLimitInvalidActionInternalErrorUnexpectedTypeUnexpectedSizeContractWasmVmContextStorageObjectCryptoEventsBudgetValueAuthError(, )\00Z\03\10\00\06\00\00\00`\03\10\00\02\00\00\00b\03\10\00\01\00\00\00, #\00Z\03\10\00\06\00\00\00|\03\10\00\03\00\00\00b\03\10\00\01\00\00\00Error(#\00\98\03\10\00\07\00\00\00`\03\10\00\02\00\00\00b\03\10\00\01\00\00\00\98\03\10\00\07\00\00\00|\03\10\00\03\00\00\00b\03\10\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\07\00\00\00called `Result::unwrap()` on an `Err` value\00\00\00\00\00\08\00\00\00\08\00\00\00\08\00\00\00ConversionError\00\08\00\00\00\06\00\00\00\07\00\00\00\07\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\05\00\00\00\04\00\00\00\1d\03\10\00%\03\10\00+\03\10\002\03\10\009\03\10\00?\03\10\00E\03\10\00K\03\10\00Q\03\10\00V\03\10\00\0b\00\00\00\0b\00\00\00\0c\00\00\00\0c\00\00\00\0d\00\00\00\0d\00\00\00\0d\00\00\00\0d\00\00\00\0e\00\00\00\0e\00\00\00\9f\02\10\00\aa\02\10\00\b5\02\10\00\c1\02\10\00\cd\02\10\00\da\02\10\00\e7\02\10\00\f4\02\10\00\01\03\10\00\0f\03\10\00"))
