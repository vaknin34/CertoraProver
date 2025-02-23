(module $soroban_timelock_contract.wasm
  (type $t0 (func (param i32 i32) (result i32)))
  (type $t1 (func (param i32 i32 i32) (result i32)))
  (type $t2 (func (param i64) (result i64)))
  (type $t3 (func (param i64 i64) (result i64)))
  (type $t4 (func (param i64 i64 i64) (result i64)))
  (type $t5 (func (result i64)))
  (type $t6 (func (param i64 i64 i64 i64) (result i64)))
  (type $t7 (func (param i32) (result i64)))
  (type $t8 (func (param i32 i32) (result i64)))
  (type $t9 (func (param i32 i64)))
  (type $t10 (func (param i64 i32 i32 i32 i32)))
  (type $t11 (func (param i64 i64 i64 i64 i64) (result i64)))
  (type $t12 (func (param i64) (result i32)))
  (type $t13 (func (param i64 i64 i64 i64 i64)))
  (type $t14 (func))
  (type $t15 (func (param i32 i32 i32 i32) (result i64)))
  (type $t16 (func (param i64 i64)))
  (type $t17 (func (param i32 i32)))
  (type $t18 (func (param i32 i32 i32 i32) (result i32)))
  (import "v" "3" (func $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE (type $t2)))
  (import "v" "1" (func $_ZN17soroban_env_guest5guest3vec7vec_get17he3c7204fed333c8fE (type $t3)))
  (import "b" "m" (func $_ZN17soroban_env_guest5guest3buf29symbol_index_in_linear_memory17hbc21e0d3e948fc5aE (type $t4)))
  (import "i" "0" (func $_ZN17soroban_env_guest5guest3int10obj_to_u6417hbf5c3deb673f2b1eE (type $t2)))
  (import "a" "0" (func $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE (type $t2)))
  (import "x" "7" (func $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h145672d3b76b8d44E (type $t5)))
  (import "i" "_" (func $_ZN17soroban_env_guest5guest3int12obj_from_u6417hac407588800da53fE (type $t2)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E (type $t3)))
  (import "x" "4" (func $_ZN17soroban_env_guest5guest7context20get_ledger_timestamp17h8c7151259f974523E (type $t5)))
  (import "v" "d" (func $_ZN17soroban_env_guest5guest3vec18vec_first_index_of17hd3f96cf96f016034E (type $t3)))
  (import "l" "2" (func $_ZN17soroban_env_guest5guest6ledger17del_contract_data17h238b702602d7ddefE (type $t3)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE (type $t3)))
  (import "i" "8" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_hi6417h96047db195ed49dfE (type $t2)))
  (import "i" "7" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_lo6417hda737eee8cb86207E (type $t2)))
  (import "i" "6" (func $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17ha9df624d96cf2a1dE (type $t3)))
  (import "b" "j" (func $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h65f4c5e4b5b0b386E (type $t3)))
  (import "m" "9" (func $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17h999916ef23111b0dE (type $t4)))
  (import "m" "a" (func $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h15a7786289874722E (type $t6)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE (type $t3)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E (type $t4)))
  (import "d" "_" (func $_ZN17soroban_env_guest5guest4call4call17he38ff75d18335ef7E (type $t4)))
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17ha93ac1edfa815407E (type $t7) (param $p0 i32) (result i64)
    (local $l1 i32) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i32.const 255
        i32.and
        br_if 0 (;@2;)
        i32.const 1048576
        i32.const 4
        call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
        local.set $l2
        br 1 (;@1;)
      end
      i32.const 1048580
      i32.const 7
      call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
      local.set $l2
    end
    local.get $l1
    local.get $l2
    call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hc9edc6ca78ef8c1fE
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
    local.set $l2
    local.get $l1
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l2)
  (func $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE (type $t8) (param $p0 i32) (param $p1 i32) (result i64)
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
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hc9edc6ca78ef8c1fE (type $t9) (param $p0 i32) (param $p1 i64)
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
    i32.const 8
    i32.add
    i32.const 1
    call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E
    i64.store offset=8
    local.get $p0
    i64.const 0
    i64.store
    local.get $l2
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E (type $t8) (param $p0 i32) (param $p1 i32) (result i64)
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
  (func $_ZN156_$LT$soroban_timelock_contract..TimeBound$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h3aaabd693b657054E (type $t9) (param $p0 i32) (param $p1 i64)
    (local $l2 i32) (local $l3 i32) (local $l4 i32) (local $l5 i32)
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
          block  ;; label = @4
            local.get $p1
            i64.const 255
            i64.and
            i64.const 76
            i64.ne
            br_if 0 (;@4;)
            i32.const 2
            local.set $l3
            local.get $p1
            i32.const 1048632
            i32.const 2
            local.get $l2
            i32.const 2
            call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17hce3ed893cada20d8E
            local.get $l2
            i64.load
            local.tee $p1
            i64.const 255
            i64.and
            i64.const 75
            i64.ne
            br_if 2 (;@2;)
            local.get $p1
            call $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE
            i64.const 32
            i64.shr_u
            i32.wrap_i64
            local.tee $l4
            i32.eqz
            br_if 2 (;@2;)
            block  ;; label = @5
              local.get $p1
              i64.const 4
              call $_ZN17soroban_env_guest5guest3vec7vec_get17he3c7204fed333c8fE
              local.tee $p1
              i32.wrap_i64
              i32.const 255
              i32.and
              local.tee $l5
              i32.const 74
              i32.eq
              br_if 0 (;@5;)
              local.get $l5
              i32.const 14
              i32.ne
              br_if 3 (;@2;)
            end
            block  ;; label = @5
              block  ;; label = @6
                local.get $p1
                i32.const 1048600
                i64.extend_i32_u
                i64.const 32
                i64.shl
                i64.const 4
                i64.or
                i64.const 8589934596
                call $_ZN17soroban_env_guest5guest3buf29symbol_index_in_linear_memory17hbc21e0d3e948fc5aE
                i64.const 32
                i64.shr_u
                i32.wrap_i64
                br_table 0 (;@6;) 1 (;@5;) 4 (;@2;)
              end
              i32.const 1
              local.get $l4
              call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
              br_if 3 (;@2;)
              i32.const 0
              local.set $l5
              br 2 (;@3;)
            end
            i32.const 1
            local.set $l5
            i32.const 1
            local.get $l4
            call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
            i32.eqz
            br_if 1 (;@3;)
            br 2 (;@2;)
          end
          i32.const 2
          local.set $l3
          br 1 (;@2;)
        end
        block  ;; label = @3
          local.get $l2
          i64.load offset=8
          local.tee $p1
          i32.wrap_i64
          i32.const 255
          i32.and
          local.tee $l4
          i32.const 64
          i32.eq
          br_if 0 (;@3;)
          local.get $l4
          i32.const 6
          i32.ne
          br_if 1 (;@2;)
          local.get $p1
          i64.const 8
          i64.shr_u
          local.set $p1
          local.get $l5
          local.set $l3
          br 2 (;@1;)
        end
        local.get $p1
        call $_ZN17soroban_env_guest5guest3int10obj_to_u6417hbf5c3deb673f2b1eE
        local.set $p1
        local.get $l5
        local.set $l3
        br 1 (;@1;)
      end
    end
    local.get $p0
    local.get $l3
    i32.store8 offset=8
    local.get $p0
    local.get $p1
    i64.store
    local.get $l2
    i32.const 16
    i32.add
    global.set $__stack_pointer)
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
  (func $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E (type $t0) (param $p0 i32) (param $p1 i32) (result i32)
    block  ;; label = @1
      local.get $p1
      local.get $p0
      i32.lt_u
      br_if 0 (;@1;)
      local.get $p1
      local.get $p0
      i32.sub
      return
    end
    call $_ZN4core9panicking11panic_const24panic_const_sub_overflow17hddb96f4b6b3b1af0E
    unreachable)
  (func $deposit (type $t11) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64) (result i64)
    (local $l5 i32) (local $l6 i64) (local $l7 i32)
    global.get $__stack_pointer
    i32.const 80
    i32.sub
    local.tee $l5
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
      local.get $l5
      i32.const 32
      i32.add
      local.get $p2
      call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
      local.get $l5
      i64.load offset=32
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
      i32.const 48
      i32.add
      i64.load
      local.set $p2
      local.get $l5
      i64.load offset=40
      local.set $l6
      local.get $l5
      i32.const 16
      i32.add
      local.get $p4
      call $_ZN156_$LT$soroban_timelock_contract..TimeBound$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h3aaabd693b657054E
      local.get $l5
      i32.load8_u offset=24
      local.tee $l7
      i32.const 2
      i32.eq
      br_if 0 (;@1;)
      local.get $l5
      i64.load offset=16
      local.set $p4
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            local.get $p3
            call $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE
            i64.const 32
            i64.shr_u
            i32.wrap_i64
            i32.const 10
            i32.gt_u
            br_if 0 (;@4;)
            i32.const 0
            call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17ha93ac1edfa815407E
            call $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE
            br_if 0 (;@4;)
            local.get $p0
            call $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE
            drop
            local.get $p1
            local.get $p0
            call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h145672d3b76b8d44E
            local.get $l6
            local.get $p2
            call $_ZN11soroban_sdk5token11TokenClient8transfer17hcda477fbab82fc4dE
            i32.const 1
            call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17ha93ac1edfa815407E
            local.set $p0
            local.get $l6
            local.get $p2
            call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h36445e94b15e4b89E
            local.set $p2
            block  ;; label = @5
              block  ;; label = @6
                local.get $l7
                i32.const 1
                i32.and
                i32.eqz
                br_if 0 (;@6;)
                i32.const 1048593
                i32.const 5
                call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
                local.set $l6
                br 1 (;@5;)
              end
              i32.const 1048587
              i32.const 6
              call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
              local.set $l6
            end
            local.get $l5
            local.get $l6
            call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hc9edc6ca78ef8c1fE
            local.get $l5
            i64.load offset=8
            local.set $l6
            local.get $p4
            i64.const 72057594037927935
            i64.gt_u
            br_if 1 (;@3;)
            local.get $p4
            i64.const 8
            i64.shl
            i64.const 6
            i64.or
            local.set $p4
            br 2 (;@2;)
          end
          call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
          unreachable
        end
        local.get $p4
        call $_ZN17soroban_env_guest5guest3int12obj_from_u6417hac407588800da53fE
        local.set $p4
      end
      local.get $l5
      local.get $p4
      i64.store offset=72
      local.get $l5
      local.get $l6
      i64.store offset=64
      i32.const 1048632
      i32.const 2
      local.get $l5
      i32.const 64
      i32.add
      i32.const 2
      call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h6aaf488d9a7738b5E
      local.set $l6
      local.get $l5
      local.get $p1
      i64.store offset=56
      local.get $l5
      local.get $l6
      i64.store offset=48
      local.get $l5
      local.get $p3
      i64.store offset=40
      local.get $l5
      local.get $p2
      i64.store offset=32
      local.get $p0
      i32.const 1048680
      i32.const 4
      local.get $l5
      i32.const 32
      i32.add
      i32.const 4
      call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h6aaf488d9a7738b5E
      call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$17put_contract_data17hc440e736fad672cdE
      i32.const 0
      call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17ha93ac1edfa815407E
      i64.const 2
      call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$17put_contract_data17hc440e736fad672cdE
      local.get $l5
      i32.const 80
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    unreachable
    unreachable)
  (func $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE (type $t9) (param $p0 i32) (param $p1 i64)
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
  (func $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE (type $t12) (param $p0 i64) (result i32)
    local.get $p0
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE
    i64.const 1
    i64.eq)
  (func $_ZN11soroban_sdk5token11TokenClient8transfer17hcda477fbab82fc4dE (type $t13) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64)
    (local $l5 i32) (local $l6 i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l5
    global.set $__stack_pointer
    local.get $l5
    local.get $p3
    local.get $p4
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h36445e94b15e4b89E
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
    i32.const 1049216
    call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
    unreachable)
  (func $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h36445e94b15e4b89E (type $t3) (param $p0 i64) (param $p1 i64) (result i64)
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
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t14)
    unreachable
    unreachable)
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h6aaf488d9a7738b5E (type $t15) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (result i64)
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
  (func $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$17put_contract_data17hc440e736fad672cdE (type $t16) (param $p0 i64) (param $p1 i64)
    local.get $p0
    local.get $p1
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E
    drop)
  (func $claim (type $t2) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i64) (local $l3 i32) (local $l4 i64) (local $l5 i64) (local $l6 i64) (local $l7 i64) (local $l8 i64) (local $l9 i32)
    global.get $__stack_pointer
    i32.const 80
    i32.sub
    local.tee $l1
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
          local.get $p0
          call $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE
          drop
          i32.const 1
          call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17ha93ac1edfa815407E
          local.tee $l2
          call $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE
          i32.eqz
          br_if 1 (;@2;)
          local.get $l2
          i64.const 2
          call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E
          local.set $l2
          i32.const 0
          local.set $l3
          block  ;; label = @4
            loop  ;; label = @5
              local.get $l3
              i32.const 32
              i32.eq
              br_if 1 (;@4;)
              local.get $l1
              i32.const 24
              i32.add
              local.get $l3
              i32.add
              i64.const 2
              i64.store
              local.get $l3
              i32.const 8
              i32.add
              local.set $l3
              br 0 (;@5;)
            end
          end
          local.get $l2
          i64.const 255
          i64.and
          i64.const 76
          i64.ne
          br_if 0 (;@3;)
          local.get $l2
          i32.const 1048680
          i32.const 4
          local.get $l1
          i32.const 24
          i32.add
          i32.const 4
          call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17hce3ed893cada20d8E
          local.get $l1
          i32.const 56
          i32.add
          local.get $l1
          i64.load offset=24
          call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
          local.get $l1
          i64.load offset=56
          i64.eqz
          i32.eqz
          br_if 0 (;@3;)
          local.get $l1
          i64.load offset=32
          local.tee $l4
          i64.const 255
          i64.and
          i64.const 75
          i64.ne
          br_if 0 (;@3;)
          local.get $l1
          i32.const 72
          i32.add
          i64.load
          local.set $l5
          local.get $l1
          i64.load offset=64
          local.set $l6
          local.get $l1
          i32.const 8
          i32.add
          local.get $l1
          i64.load offset=40
          call $_ZN156_$LT$soroban_timelock_contract..TimeBound$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h3aaabd693b657054E
          local.get $l1
          i32.load8_u offset=16
          local.tee $l3
          i32.const 2
          i32.eq
          br_if 0 (;@3;)
          local.get $l1
          i64.load offset=48
          local.tee $l7
          i64.const 255
          i64.and
          i64.const 77
          i64.ne
          br_if 0 (;@3;)
          local.get $l1
          i64.load offset=8
          local.set $l2
          block  ;; label = @4
            block  ;; label = @5
              call $_ZN17soroban_env_guest5guest7context20get_ledger_timestamp17h8c7151259f974523E
              local.tee $l8
              i32.wrap_i64
              i32.const 255
              i32.and
              local.tee $l9
              i32.const 64
              i32.eq
              br_if 0 (;@5;)
              block  ;; label = @6
                local.get $l9
                i32.const 6
                i32.ne
                br_if 0 (;@6;)
                local.get $l8
                i64.const 8
                i64.shr_u
                local.set $l8
                br 2 (;@4;)
              end
              local.get $l1
              i32.const 24
              i32.add
              i32.const 1049232
              call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
              unreachable
            end
            local.get $l8
            call $_ZN17soroban_env_guest5guest3int10obj_to_u6417hbf5c3deb673f2b1eE
            local.set $l8
          end
          local.get $l8
          local.get $l2
          i64.ge_u
          local.get $l8
          local.get $l2
          i64.le_u
          local.get $l3
          i32.const 1
          i32.and
          select
          i32.eqz
          br_if 2 (;@1;)
          local.get $l4
          local.get $p0
          call $_ZN17soroban_env_guest5guest3vec18vec_first_index_of17hd3f96cf96f016034E
          i64.const 2
          i64.eq
          br_if 2 (;@1;)
          local.get $l7
          call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h145672d3b76b8d44E
          local.get $p0
          local.get $l6
          local.get $l5
          call $_ZN11soroban_sdk5token11TokenClient8transfer17hcda477fbab82fc4dE
          i32.const 1
          call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17ha93ac1edfa815407E
          i64.const 2
          call $_ZN17soroban_env_guest5guest6ledger17del_contract_data17h238b702602d7ddefE
          drop
          local.get $l1
          i32.const 80
          i32.add
          global.set $__stack_pointer
          i64.const 2
          return
        end
        unreachable
        unreachable
      end
      call $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E
      unreachable
    end
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core6result13unwrap_failed17h472431483d5eea7fE (type $t17) (param $p0 i32) (param $p1 i32)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E (type $t14)
    call $_ZN4core9panicking11panic_const24panic_const_sub_overflow17hddb96f4b6b3b1af0E
    unreachable)
  (func $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E (type $t18) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (result i32)
    (local $l4 i32)
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p2
          i32.const 1114112
          i32.eq
          br_if 0 (;@3;)
          i32.const 1
          local.set $l4
          local.get $p0
          local.get $p2
          local.get $p1
          i32.load offset=16
          call_indirect $T0 (type $t0)
          br_if 1 (;@2;)
        end
        local.get $p3
        br_if 1 (;@1;)
        i32.const 0
        local.set $l4
      end
      local.get $l4
      return
    end
    local.get $p0
    local.get $p3
    i32.const 0
    local.get $p1
    i32.load offset=12
    call_indirect $T0 (type $t1))
  (func $_ZN4core3fmt9Formatter3pad17hdad3e25ba05328b0E (type $t1) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
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
            call_indirect $T0 (type $t1)
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
        call_indirect $T0 (type $t1)
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
          call_indirect $T0 (type $t0)
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
      call_indirect $T0 (type $t1)
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
      call_indirect $T0 (type $t1)
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
          call_indirect $T0 (type $t0)
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
  (func $_ZN4core9panicking11panic_const24panic_const_sub_overflow17hddb96f4b6b3b1af0E (type $t14)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i32$GT$3fmt17hd6308d8453dcc3baE (type $t0) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32) (local $l3 i32) (local $l4 i32) (local $l5 i64) (local $l6 i64) (local $l7 i32) (local $l8 i32) (local $l9 i32) (local $l10 i32) (local $l11 i32) (local $l12 i32) (local $l13 i32) (local $l14 i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $p0
    i32.load
    local.tee $l3
    local.get $l3
    i32.const 31
    i32.shr_s
    local.tee $p0
    i32.xor
    local.get $p0
    i32.sub
    local.tee $l4
    i64.extend_i32_u
    local.set $l5
    i32.const 39
    local.set $p0
    block  ;; label = @1
      block  ;; label = @2
        local.get $l4
        i32.const 10000
        i32.ge_u
        br_if 0 (;@2;)
        local.get $l5
        local.set $l6
        br 1 (;@1;)
      end
      i32.const 39
      local.set $p0
      loop  ;; label = @2
        local.get $l2
        i32.const 9
        i32.add
        local.get $p0
        i32.add
        local.tee $l4
        i32.const -4
        i32.add
        local.get $l5
        i64.const 10000
        i64.div_u
        local.tee $l6
        i64.const 55536
        i64.mul
        local.get $l5
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
        i32.const 1048712
        i32.add
        i32.load16_u align=1
        i32.store16 align=1
        local.get $l4
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
        i32.const 1048712
        i32.add
        i32.load16_u align=1
        i32.store16 align=1
        local.get $p0
        i32.const -4
        i32.add
        local.set $p0
        local.get $l5
        i64.const 99999999
        i64.gt_u
        local.set $l4
        local.get $l6
        local.set $l5
        local.get $l4
        br_if 0 (;@2;)
      end
    end
    block  ;; label = @1
      local.get $l6
      i32.wrap_i64
      local.tee $l4
      i32.const 99
      i32.le_u
      br_if 0 (;@1;)
      local.get $l2
      i32.const 9
      i32.add
      local.get $p0
      i32.const -2
      i32.add
      local.tee $p0
      i32.add
      local.get $l6
      i32.wrap_i64
      local.tee $l7
      i32.const 65535
      i32.and
      i32.const 100
      i32.div_u
      local.tee $l4
      i32.const -100
      i32.mul
      local.get $l7
      i32.add
      i32.const 65535
      i32.and
      i32.const 1
      i32.shl
      i32.const 1048712
      i32.add
      i32.load16_u align=1
      i32.store16 align=1
    end
    block  ;; label = @1
      block  ;; label = @2
        local.get $l4
        i32.const 10
        i32.lt_u
        br_if 0 (;@2;)
        local.get $l2
        i32.const 9
        i32.add
        local.get $p0
        i32.const -2
        i32.add
        local.tee $p0
        i32.add
        local.get $l4
        i32.const 1
        i32.shl
        i32.const 1048712
        i32.add
        i32.load16_u align=1
        i32.store16 align=1
        br 1 (;@1;)
      end
      local.get $l2
      i32.const 9
      i32.add
      local.get $p0
      i32.const -1
      i32.add
      local.tee $p0
      i32.add
      local.get $l4
      i32.const 48
      i32.or
      i32.store8
    end
    i32.const 39
    local.get $p0
    i32.sub
    local.set $l9
    block  ;; label = @1
      block  ;; label = @2
        local.get $l3
        i32.const -1
        i32.gt_s
        br_if 0 (;@2;)
        i32.const 40
        local.get $p0
        i32.sub
        local.set $l7
        local.get $p1
        i32.load offset=28
        local.set $l4
        i32.const 45
        local.set $l3
        br 1 (;@1;)
      end
      i32.const 43
      i32.const 1114112
      local.get $p1
      i32.load offset=28
      local.tee $l4
      i32.const 1
      i32.and
      local.tee $l7
      select
      local.set $l3
      local.get $l7
      local.get $l9
      i32.add
      local.set $l7
    end
    local.get $l2
    i32.const 9
    i32.add
    local.get $p0
    i32.add
    local.set $l10
    local.get $l4
    i32.const 4
    i32.and
    i32.const 2
    i32.shr_u
    local.set $l11
    block  ;; label = @1
      block  ;; label = @2
        local.get $p1
        i32.load
        br_if 0 (;@2;)
        i32.const 1
        local.set $p0
        local.get $p1
        i32.load offset=20
        local.tee $l4
        local.get $p1
        i32.load offset=24
        local.tee $l7
        local.get $l3
        local.get $l11
        call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
        br_if 1 (;@1;)
        local.get $l4
        local.get $l10
        local.get $l9
        local.get $l7
        i32.load offset=12
        call_indirect $T0 (type $t1)
        local.set $p0
        br 1 (;@1;)
      end
      block  ;; label = @2
        local.get $p1
        i32.load offset=4
        local.tee $l12
        local.get $l7
        i32.gt_u
        br_if 0 (;@2;)
        i32.const 1
        local.set $p0
        local.get $p1
        i32.load offset=20
        local.tee $l4
        local.get $p1
        i32.load offset=24
        local.tee $l7
        local.get $l3
        local.get $l11
        call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
        br_if 1 (;@1;)
        local.get $l4
        local.get $l10
        local.get $l9
        local.get $l7
        i32.load offset=12
        call_indirect $T0 (type $t1)
        local.set $p0
        br 1 (;@1;)
      end
      block  ;; label = @2
        local.get $l4
        i32.const 8
        i32.and
        i32.eqz
        br_if 0 (;@2;)
        local.get $p1
        i32.load offset=16
        local.set $l13
        local.get $p1
        i32.const 48
        i32.store offset=16
        local.get $p1
        i32.load8_u offset=32
        local.set $l14
        i32.const 1
        local.set $p0
        local.get $p1
        i32.const 1
        i32.store8 offset=32
        local.get $p1
        i32.load offset=20
        local.tee $l4
        local.get $p1
        i32.load offset=24
        local.tee $l8
        local.get $l3
        local.get $l11
        call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
        br_if 1 (;@1;)
        local.get $l12
        local.get $l7
        i32.sub
        i32.const 1
        i32.add
        local.set $p0
        block  ;; label = @3
          loop  ;; label = @4
            local.get $p0
            i32.const -1
            i32.add
            local.tee $p0
            i32.eqz
            br_if 1 (;@3;)
            local.get $l4
            i32.const 48
            local.get $l8
            i32.load offset=16
            call_indirect $T0 (type $t0)
            i32.eqz
            br_if 0 (;@4;)
          end
          i32.const 1
          local.set $p0
          br 2 (;@1;)
        end
        i32.const 1
        local.set $p0
        local.get $l4
        local.get $l10
        local.get $l9
        local.get $l8
        i32.load offset=12
        call_indirect $T0 (type $t1)
        br_if 1 (;@1;)
        local.get $p1
        local.get $l14
        i32.store8 offset=32
        local.get $p1
        local.get $l13
        i32.store offset=16
        i32.const 0
        local.set $p0
        br 1 (;@1;)
      end
      local.get $l12
      local.get $l7
      i32.sub
      local.set $l12
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            local.get $p1
            i32.load8_u offset=32
            local.tee $p0
            br_table 2 (;@2;) 0 (;@4;) 1 (;@3;) 0 (;@4;) 2 (;@2;)
          end
          local.get $l12
          local.set $p0
          i32.const 0
          local.set $l12
          br 1 (;@2;)
        end
        local.get $l12
        i32.const 1
        i32.shr_u
        local.set $p0
        local.get $l12
        i32.const 1
        i32.add
        i32.const 1
        i32.shr_u
        local.set $l12
      end
      local.get $p0
      i32.const 1
      i32.add
      local.set $p0
      local.get $p1
      i32.load offset=16
      local.set $l8
      local.get $p1
      i32.load offset=24
      local.set $l4
      local.get $p1
      i32.load offset=20
      local.set $l7
      block  ;; label = @2
        loop  ;; label = @3
          local.get $p0
          i32.const -1
          i32.add
          local.tee $p0
          i32.eqz
          br_if 1 (;@2;)
          local.get $l7
          local.get $l8
          local.get $l4
          i32.load offset=16
          call_indirect $T0 (type $t0)
          i32.eqz
          br_if 0 (;@3;)
        end
        i32.const 1
        local.set $p0
        br 1 (;@1;)
      end
      i32.const 1
      local.set $p0
      local.get $l7
      local.get $l4
      local.get $l3
      local.get $l11
      call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
      br_if 0 (;@1;)
      local.get $l7
      local.get $l10
      local.get $l9
      local.get $l4
      i32.load offset=12
      call_indirect $T0 (type $t1)
      br_if 0 (;@1;)
      i32.const 0
      local.set $p0
      loop  ;; label = @2
        block  ;; label = @3
          local.get $l12
          local.get $p0
          i32.ne
          br_if 0 (;@3;)
          local.get $l12
          local.get $l12
          i32.lt_u
          local.set $p0
          br 2 (;@1;)
        end
        local.get $p0
        i32.const 1
        i32.add
        local.set $p0
        local.get $l7
        local.get $l8
        local.get $l4
        i32.load offset=16
        call_indirect $T0 (type $t0)
        i32.eqz
        br_if 0 (;@2;)
      end
      local.get $p0
      i32.const -1
      i32.add
      local.get $l12
      i32.lt_u
      local.set $p0
    end
    local.get $l2
    i32.const 48
    i32.add
    global.set $__stack_pointer
    local.get $p0)
  (func $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17hb37de2cca199de8bE (type $t0) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p1
    local.get $p0
    i32.load
    local.get $p0
    i32.load offset=4
    call $_ZN4core3fmt9Formatter3pad17hdad3e25ba05328b0E)
  (func $_ZN69_$LT$soroban_env_common..error..Error$u20$as$u20$core..fmt..Debug$GT$3fmt17h2f2be93d53eefd32E (type $t0) (param $p0 i32) (param $p1 i32) (result i32)
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
            call $_ZN11stellar_xdr4curr9generated11ScErrorType4name17h419699d3f4325e34E
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
              call $_ZN11stellar_xdr4curr9generated11ScErrorCode4name17h04c17a0e8b1b13b8E
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
              i32.const 1049108
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
            i32.const 1049136
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
          i32.const 1049192
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
        call $_ZN11stellar_xdr4curr9generated11ScErrorType4name17h419699d3f4325e34E
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
        i32.const 1049136
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
      call $_ZN11stellar_xdr4curr9generated11ScErrorCode4name17h04c17a0e8b1b13b8E
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
      i32.const 1049168
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
  (func $_ZN11stellar_xdr4curr9generated11ScErrorType4name17h419699d3f4325e34E (type $t17) (param $p0 i32) (param $p1 i32)
    local.get $p0
    local.get $p1
    i32.const 2
    i32.shl
    local.tee $p1
    i32.const 1049264
    i32.add
    i32.load
    i32.store offset=4
    local.get $p0
    local.get $p1
    i32.const 1049304
    i32.add
    i32.load
    i32.store)
  (func $_ZN11stellar_xdr4curr9generated11ScErrorCode4name17h04c17a0e8b1b13b8E (type $t17) (param $p0 i32) (param $p1 i32)
    local.get $p0
    local.get $p1
    i32.const 2
    i32.shl
    local.tee $p1
    i32.const 1049344
    i32.add
    i32.load
    i32.store offset=4
    local.get $p0
    local.get $p1
    i32.const 1049384
    i32.add
    i32.load
    i32.store)
  (func $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE (type $t1) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32) (local $l7 i32) (local $l8 i32) (local $l9 i32) (local $l10 i32) (local $l11 i32) (local $l12 i32) (local $l13 i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    block  ;; label = @1
      local.get $p2
      i32.load offset=4
      local.tee $l4
      br_table 0 (;@1;) 0 (;@1;) 0 (;@1;)
    end
    local.get $p2
    i32.load offset=12
    local.set $l5
    local.get $p2
    i32.load
    local.set $l6
    local.get $l3
    i32.const 3
    i32.store8 offset=44
    local.get $l3
    i32.const 32
    i32.store offset=28
    i32.const 0
    local.set $l7
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
              local.tee $l8
              br_if 0 (;@5;)
              local.get $l5
              i32.eqz
              br_if 1 (;@4;)
              local.get $p2
              i32.load offset=8
              local.set $p2
              local.get $l5
              i32.const 3
              i32.shl
              local.set $p0
              local.get $l5
              i32.const -1
              i32.add
              i32.const 536870911
              i32.and
              i32.const 1
              i32.add
              local.set $l7
              local.get $l6
              local.set $p1
              loop  ;; label = @6
                block  ;; label = @7
                  local.get $p1
                  i32.const 4
                  i32.add
                  i32.load
                  local.tee $l5
                  i32.eqz
                  br_if 0 (;@7;)
                  local.get $l3
                  i32.load offset=32
                  local.get $p1
                  i32.load
                  local.get $l5
                  local.get $l3
                  i32.load offset=36
                  i32.load offset=12
                  call_indirect $T0 (type $t1)
                  br_if 4 (;@3;)
                end
                local.get $p2
                i32.load
                local.get $l3
                i32.const 12
                i32.add
                local.get $p2
                i32.load offset=4
                call_indirect $T0 (type $t0)
                br_if 3 (;@3;)
                local.get $p2
                i32.const 8
                i32.add
                local.set $p2
                local.get $p1
                i32.const 8
                i32.add
                local.set $p1
                local.get $p0
                i32.const -8
                i32.add
                local.tee $p0
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
            local.set $l9
            local.get $p1
            i32.const -1
            i32.add
            i32.const 134217727
            i32.and
            i32.const 1
            i32.add
            local.set $l7
            local.get $p2
            i32.load offset=8
            local.set $l10
            i32.const 0
            local.set $p0
            local.get $l6
            local.set $p1
            loop  ;; label = @5
              block  ;; label = @6
                local.get $p1
                i32.const 4
                i32.add
                i32.load
                local.tee $p2
                i32.eqz
                br_if 0 (;@6;)
                local.get $l3
                i32.load offset=32
                local.get $p1
                i32.load
                local.get $p2
                local.get $l3
                i32.load offset=36
                i32.load offset=12
                call_indirect $T0 (type $t1)
                br_if 3 (;@3;)
              end
              local.get $l3
              local.get $l8
              local.get $p0
              i32.add
              local.tee $p2
              i32.const 16
              i32.add
              i32.load
              i32.store offset=28
              local.get $l3
              local.get $p2
              i32.const 28
              i32.add
              i32.load8_u
              i32.store8 offset=44
              local.get $l3
              local.get $p2
              i32.const 24
              i32.add
              i32.load
              i32.store offset=40
              local.get $p2
              i32.const 12
              i32.add
              i32.load
              local.set $l5
              i32.const 0
              local.set $l11
              i32.const 0
              local.set $l12
              block  ;; label = @6
                block  ;; label = @7
                  block  ;; label = @8
                    local.get $p2
                    i32.const 8
                    i32.add
                    i32.load
                    br_table 1 (;@7;) 0 (;@8;) 2 (;@6;) 1 (;@7;)
                  end
                  local.get $l5
                  i32.const 3
                  i32.shl
                  local.set $l13
                  i32.const 0
                  local.set $l12
                  local.get $l10
                  local.get $l13
                  i32.add
                  local.tee $l13
                  i32.load offset=4
                  br_if 1 (;@6;)
                  local.get $l13
                  i32.load
                  local.set $l5
                end
                i32.const 1
                local.set $l12
              end
              local.get $l3
              local.get $l5
              i32.store offset=16
              local.get $l3
              local.get $l12
              i32.store offset=12
              local.get $p2
              i32.const 4
              i32.add
              i32.load
              local.set $l5
              block  ;; label = @6
                block  ;; label = @7
                  block  ;; label = @8
                    local.get $p2
                    i32.load
                    br_table 1 (;@7;) 0 (;@8;) 2 (;@6;) 1 (;@7;)
                  end
                  local.get $l5
                  i32.const 3
                  i32.shl
                  local.set $l12
                  local.get $l10
                  local.get $l12
                  i32.add
                  local.tee $l12
                  i32.load offset=4
                  br_if 1 (;@6;)
                  local.get $l12
                  i32.load
                  local.set $l5
                end
                i32.const 1
                local.set $l11
              end
              local.get $l3
              local.get $l5
              i32.store offset=24
              local.get $l3
              local.get $l11
              i32.store offset=20
              local.get $l10
              local.get $p2
              i32.const 20
              i32.add
              i32.load
              i32.const 3
              i32.shl
              i32.add
              local.tee $p2
              i32.load
              local.get $l3
              i32.const 12
              i32.add
              local.get $p2
              i32.load offset=4
              call_indirect $T0 (type $t0)
              br_if 2 (;@3;)
              local.get $p1
              i32.const 8
              i32.add
              local.set $p1
              local.get $l9
              local.get $p0
              i32.const 32
              i32.add
              local.tee $p0
              i32.ne
              br_if 0 (;@5;)
            end
          end
          local.get $l7
          local.get $l4
          i32.ge_u
          br_if 1 (;@2;)
          local.get $l3
          i32.load offset=32
          local.get $l6
          local.get $l7
          i32.const 3
          i32.shl
          i32.add
          local.tee $p2
          i32.load
          local.get $p2
          i32.load offset=4
          local.get $l3
          i32.load offset=36
          i32.load offset=12
          call_indirect $T0 (type $t1)
          i32.eqz
          br_if 1 (;@2;)
        end
        i32.const 1
        local.set $p2
        br 1 (;@1;)
      end
      i32.const 0
      local.set $p2
    end
    local.get $l3
    i32.const 48
    i32.add
    global.set $__stack_pointer
    local.get $p2)
  (func $_ (type $t14))
  (func $_ZN77_$LT$soroban_env_common..val..ConversionError$u20$as$u20$core..fmt..Debug$GT$3fmt17hd509f52596321fbfE (type $t0) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p1
    i32.load offset=20
    i32.const 1049248
    i32.const 15
    local.get $p1
    i32.load offset=24
    i32.load offset=12
    call_indirect $T0 (type $t1))
  (table $T0 5 5 funcref)
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1049424))
  (global $__heap_base i32 (i32.const 1049424))
  (export "memory" (memory $memory))
  (export "deposit" (func $deposit))
  (export "claim" (func $claim))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (elem $e0 (i32.const 1) func $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17hb37de2cca199de8bE $_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i32$GT$3fmt17hd6308d8453dcc3baE $_ZN77_$LT$soroban_env_common..val..ConversionError$u20$as$u20$core..fmt..Debug$GT$3fmt17hd509f52596321fbfE $_ZN69_$LT$soroban_env_common..error..Error$u20$as$u20$core..fmt..Debug$GT$3fmt17h2f2be93d53eefd32E)
  (data $.rodata (i32.const 1048576) "InitBalanceBeforeAfter\00\00\0b\00\10\00\06\00\00\00\11\00\10\00\05\00\00\00kindtimestamp\00\00\00(\00\10\00\04\00\00\00,\00\10\00\09\00\00\00amountclaimantstime_boundtoken\00\00H\00\10\00\06\00\00\00N\00\10\00\09\00\00\00W\00\10\00\0a\00\00\00a\00\10\00\05\00\00\0000010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899ArithDomainIndexBoundsInvalidInputMissingValueExistingValueExceededLimitInvalidActionInternalErrorUnexpectedTypeUnexpectedSizeContractWasmVmContextStorageObjectCryptoEventsBudgetValueAuthError(, )\0b\02\10\00\06\00\00\00\11\02\10\00\02\00\00\00\13\02\10\00\01\00\00\00, #\00\0b\02\10\00\06\00\00\00,\02\10\00\03\00\00\00\13\02\10\00\01\00\00\00Error(#\00H\02\10\00\07\00\00\00\11\02\10\00\02\00\00\00\13\02\10\00\01\00\00\00H\02\10\00\07\00\00\00,\02\10\00\03\00\00\00\13\02\10\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\03\00\00\00\00\00\00\00\08\00\00\00\08\00\00\00\04\00\00\00ConversionError\00\08\00\00\00\06\00\00\00\07\00\00\00\07\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\05\00\00\00\04\00\00\00\ce\01\10\00\d6\01\10\00\dc\01\10\00\e3\01\10\00\ea\01\10\00\f0\01\10\00\f6\01\10\00\fc\01\10\00\02\02\10\00\07\02\10\00\0b\00\00\00\0b\00\00\00\0c\00\00\00\0c\00\00\00\0d\00\00\00\0d\00\00\00\0d\00\00\00\0d\00\00\00\0e\00\00\00\0e\00\00\00P\01\10\00[\01\10\00f\01\10\00r\01\10\00~\01\10\00\8b\01\10\00\98\01\10\00\a5\01\10\00\b2\01\10\00\c0\01\10\00"))
