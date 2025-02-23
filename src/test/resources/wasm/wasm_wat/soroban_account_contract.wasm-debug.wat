(module $soroban_account_contract.wasm
  (type $t0 (func (param i32 i32 i32) (result i32)))
  (type $t1 (func (param i32 i32) (result i32)))
  (type $t2 (func (param i64 i64) (result i64)))
  (type $t3 (func (param i64) (result i64)))
  (type $t4 (func (result i64)))
  (type $t5 (func (param i64 i64 i64) (result i64)))
  (type $t6 (func (param i64 i64 i64 i64) (result i64)))
  (type $t7 (func (param i64 i64) (result i32)))
  (type $t8 (func (param i32) (result i32)))
  (type $t9 (func (param i32 i32) (result i64)))
  (type $t10 (func (param i32 i64)))
  (type $t11 (func (param i64 i32 i32 i32 i32)))
  (type $t12 (func (param i64 i64)))
  (type $t13 (func))
  (type $t14 (func (param i32 i32)))
  (type $t15 (func (param i64) (result i32)))
  (type $t16 (func (param i64 i32 i32) (result i64)))
  (type $t17 (func (param i32 i32 i32 i32) (result i32)))
  (import "x" "0" (func $_ZN17soroban_env_guest5guest7context7obj_cmp17h189bc77d88b5cf98E (type $t2)))
  (import "b" "8" (func $_ZN17soroban_env_guest5guest3buf9bytes_len17h783b00115bb1ca2bE (type $t3)))
  (import "v" "3" (func $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE (type $t3)))
  (import "v" "1" (func $_ZN17soroban_env_guest5guest3vec7vec_get17he3c7204fed333c8fE (type $t2)))
  (import "x" "7" (func $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h145672d3b76b8d44E (type $t4)))
  (import "a" "0" (func $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE (type $t3)))
  (import "m" "_" (func $_ZN17soroban_env_guest5guest3map7map_new17h81a78b249b2dc082E (type $t4)))
  (import "m" "4" (func $_ZN17soroban_env_guest5guest3map7map_has17hc11ce5fcb08aa3f6E (type $t2)))
  (import "m" "1" (func $_ZN17soroban_env_guest5guest3map7map_get17hfaa762dc2cd709cbE (type $t2)))
  (import "m" "0" (func $_ZN17soroban_env_guest5guest3map7map_put17h27b18abb0ba80dc7E (type $t5)))
  (import "c" "0" (func $_ZN17soroban_env_guest5guest6crypto18verify_sig_ed2551917hb3129d31d3626aacE (type $t5)))
  (import "m" "a" (func $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h15a7786289874722E (type $t6)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE (type $t2)))
  (import "b" "m" (func $_ZN17soroban_env_guest5guest3buf29symbol_index_in_linear_memory17hbc21e0d3e948fc5aE (type $t5)))
  (import "i" "8" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_hi6417h96047db195ed49dfE (type $t3)))
  (import "i" "7" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_lo6417hda737eee8cb86207E (type $t3)))
  (import "b" "j" (func $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h65f4c5e4b5b0b386E (type $t2)))
  (import "i" "6" (func $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17ha9df624d96cf2a1dE (type $t2)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE (type $t2)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E (type $t2)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E (type $t5)))
  (func $_ZN4core3cmp9PartialEq2ne17hdc583e0bce855b48E (type $t7) (param $p0 i64) (param $p1 i64) (result i32)
    (local $l2 i32) (local $l3 i32) (local $l4 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p0
          i64.const 255
          i64.and
          i64.const 14
          i64.ne
          br_if 0 (;@3;)
          local.get $p1
          i64.const 255
          i64.and
          i64.const 14
          i64.eq
          br_if 1 (;@2;)
        end
        local.get $p0
        local.get $p1
        call $_ZN17soroban_env_guest5guest7context7obj_cmp17h189bc77d88b5cf98E
        i64.const 0
        i64.ne
        local.set $l3
        br 1 (;@1;)
      end
      local.get $l2
      local.get $p1
      i64.const 8
      i64.shr_u
      i64.store offset=8
      local.get $l2
      local.get $p0
      i64.const 8
      i64.shr_u
      i64.store
      block  ;; label = @2
        loop  ;; label = @3
          local.get $l2
          call $_ZN102_$LT$soroban_env_common..symbol..SymbolSmallIter$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h878e6a30a19c98faE
          local.set $l3
          local.get $l2
          i32.const 8
          i32.add
          call $_ZN102_$LT$soroban_env_common..symbol..SymbolSmallIter$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h878e6a30a19c98faE
          local.set $l4
          local.get $l3
          i32.const 1114112
          i32.eq
          br_if 1 (;@2;)
          local.get $l4
          local.get $l3
          i32.eq
          br_if 0 (;@3;)
        end
        i32.const 1
        local.set $l3
        br 1 (;@1;)
      end
      local.get $l4
      i32.const 1114112
      i32.ne
      local.set $l3
    end
    local.get $l2
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l3)
  (func $_ZN102_$LT$soroban_env_common..symbol..SymbolSmallIter$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h878e6a30a19c98faE (type $t8) (param $p0 i32) (result i32)
    (local $l1 i64) (local $l2 i32) (local $l3 i32)
    local.get $p0
    i64.load
    local.set $l1
    loop  ;; label = @1
      block  ;; label = @2
        local.get $l1
        i64.eqz
        i32.eqz
        br_if 0 (;@2;)
        i32.const 1114112
        return
      end
      block  ;; label = @2
        block  ;; label = @3
          local.get $l1
          i64.const 48
          i64.shr_u
          i32.wrap_i64
          i32.const 63
          i32.and
          local.tee $l2
          i32.const 1
          i32.ne
          br_if 0 (;@3;)
          i32.const 95
          local.set $l2
          br 1 (;@2;)
        end
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              local.get $l2
              i32.const -1
              i32.add
              i32.const 11
              i32.ge_u
              br_if 0 (;@5;)
              i32.const 46
              local.set $l3
              br 1 (;@4;)
            end
            block  ;; label = @5
              local.get $l2
              i32.const -12
              i32.add
              i32.const 26
              i32.ge_u
              br_if 0 (;@5;)
              i32.const 53
              local.set $l3
              br 1 (;@4;)
            end
            local.get $l2
            i32.const 37
            i32.le_u
            br_if 1 (;@3;)
            i32.const 59
            local.set $l3
          end
          local.get $l2
          local.get $l3
          i32.add
          local.set $l2
          br 1 (;@2;)
        end
        local.get $p0
        local.get $l1
        i64.const 6
        i64.shl
        local.tee $l1
        i64.store
        br 1 (;@1;)
      end
    end
    local.get $p0
    local.get $l1
    i64.const 6
    i64.shl
    i64.store
    local.get $l2)
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h1f50ce4880217dc2E (type $t2) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            local.get $p0
            i32.wrap_i64
            br_table 2 (;@2;) 0 (;@4;) 1 (;@3;) 2 (;@2;)
          end
          i32.const 1048713
          i32.const 6
          call $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17h1647bdd1d3a8fa36E
          local.get $p1
          call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h5bb243f4c9a8fdcaE
          local.set $p0
          br 2 (;@1;)
        end
        i32.const 1048719
        i32.const 10
        call $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17h1647bdd1d3a8fa36E
        local.get $p1
        call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h5bb243f4c9a8fdcaE
        local.set $p0
        br 1 (;@1;)
      end
      local.get $l2
      i32.const 1048704
      i32.const 9
      call $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17h1647bdd1d3a8fa36E
      i64.store offset=8
      local.get $l2
      i32.const 8
      i32.add
      i32.const 1
      call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E
      local.set $p0
    end
    local.get $l2
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $p0)
  (func $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17h1647bdd1d3a8fa36E (type $t9) (param $p0 i32) (param $p1 i32) (result i64)
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
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h5bb243f4c9a8fdcaE (type $t2) (param $p0 i64) (param $p1 i64) (result i64)
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
    local.get $l2
    i32.const 2
    call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E
    local.set $p1
    local.get $l2
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $p1)
  (func $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E (type $t9) (param $p0 i32) (param $p1 i32) (result i64)
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
  (func $_ZN77_$LT$soroban_env_common..val..ConversionError$u20$as$u20$core..fmt..Debug$GT$3fmt17hd509f52596321fbfE (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p1
    i32.load offset=20
    i32.const 1048644
    i32.const 15
    local.get $p1
    i32.load offset=24
    i32.load offset=12
    call_indirect $T0 (type $t0))
  (func $_ZN158_$LT$soroban_account_contract..AccSignature$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h81ea9020b451ff5bE (type $t10) (param $p0 i32) (param $p1 i64)
    (local $l2 i32) (local $l3 i32) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 32
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
        i32.const 16
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
          i32.const 1048688
          i32.const 2
          local.get $l2
          i32.const 16
          i32.add
          i32.const 2
          call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h8a577be1f73f732bE
          local.get $l2
          local.get $l2
          i64.load offset=16
          call $_ZN155_$LT$soroban_sdk..bytes..BytesN$LT$_$GT$$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h44db584ecfeb8fbeE
          local.get $l2
          i32.load
          br_if 1 (;@2;)
          block  ;; label = @4
            local.get $l2
            i64.load offset=24
            local.tee $p1
            i64.const 255
            i64.and
            i64.const 72
            i64.ne
            br_if 0 (;@4;)
            local.get $l2
            i64.load offset=8
            local.set $l4
            local.get $p1
            call $_ZN17soroban_env_guest5guest3buf9bytes_len17h783b00115bb1ca2bE
            i64.const -4294967296
            i64.and
            i64.const 274877906944
            i64.ne
            br_if 0 (;@4;)
            local.get $p0
            local.get $p1
            i64.store offset=16
            local.get $p0
            local.get $l4
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
    i32.const 32
    i32.add
    global.set $__stack_pointer)
  (func $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h8a577be1f73f732bE (type $t11) (param $p0 i64) (param $p1 i32) (param $p2 i32) (param $p3 i32) (param $p4 i32)
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
  (func $_ZN155_$LT$soroban_sdk..bytes..BytesN$LT$_$GT$$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h44db584ecfeb8fbeE (type $t10) (param $p0 i32) (param $p1 i64)
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
  (func $init (type $t3) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i64) (local $l3 i64) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p0
          i64.const 255
          i64.and
          i64.const 75
          i64.ne
          br_if 0 (;@3;)
          local.get $p0
          call $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE
          i64.const 32
          i64.shr_u
          local.set $l2
          i64.const 0
          local.set $l3
          i64.const 4
          local.set $l4
          block  ;; label = @4
            loop  ;; label = @5
              local.get $l3
              local.get $l2
              i64.ge_u
              br_if 1 (;@4;)
              local.get $l1
              i32.const 8
              i32.add
              local.get $p0
              local.get $l4
              call $_ZN17soroban_env_guest5guest3vec7vec_get17he3c7204fed333c8fE
              call $_ZN155_$LT$soroban_sdk..bytes..BytesN$LT$_$GT$$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h44db584ecfeb8fbeE
              local.get $l3
              i64.const 4294967295
              i64.eq
              br_if 3 (;@2;)
              local.get $l1
              i64.load offset=8
              i32.wrap_i64
              br_if 4 (;@1;)
              i64.const 1
              local.get $l1
              i64.load offset=16
              call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h1f50ce4880217dc2E
              i64.const 2
              call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$17put_contract_data17hc440e736fad672cdE
              local.get $l4
              i64.const 4294967296
              i64.add
              local.set $l4
              local.get $l3
              i64.const 1
              i64.add
              local.set $l3
              br 0 (;@5;)
            end
          end
          local.get $p0
          call $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE
          local.set $l3
          i64.const 0
          local.get $l3
          call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h1f50ce4880217dc2E
          local.get $l3
          i64.const -4294967296
          i64.and
          i64.const 4
          i64.or
          call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$17put_contract_data17hc440e736fad672cdE
          local.get $l1
          i32.const 32
          i32.add
          global.set $__stack_pointer
          i64.const 2
          return
        end
        unreachable
        unreachable
      end
      call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
      unreachable
    end
    local.get $l1
    i32.const 31
    i32.add
    i32.const 1048612
    call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
    unreachable)
  (func $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$17put_contract_data17hc440e736fad672cdE (type $t12) (param $p0 i64) (param $p1 i64)
    local.get $p0
    local.get $p1
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E
    drop)
  (func $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E (type $t13)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core6result13unwrap_failed17h472431483d5eea7fE (type $t14) (param $p0 i32) (param $p1 i32)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $add_limit (type $t2) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32) (local $l3 i64)
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
      i32.const 8
      i32.add
      local.get $p1
      call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
      local.get $l2
      i64.load offset=8
      i64.eqz
      i32.eqz
      br_if 0 (;@1;)
      local.get $l2
      i32.const 24
      i32.add
      i64.load
      local.set $p1
      local.get $l2
      i64.load offset=16
      local.set $l3
      call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h145672d3b76b8d44E
      call $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE
      drop
      i64.const 2
      local.get $p0
      call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h1f50ce4880217dc2E
      local.get $l3
      local.get $p1
      call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17he61e6e8b3f136369E
      call $_ZN70_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..Env$GT$17put_contract_data17hc440e736fad672cdE
      local.get $l2
      i32.const 32
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    unreachable
    unreachable)
  (func $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE (type $t10) (param $p0 i32) (param $p1 i64)
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
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17he61e6e8b3f136369E (type $t2) (param $p0 i64) (param $p1 i64) (result i64)
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
  (func $__check_auth (type $t5) (param $p0 i64) (param $p1 i64) (param $p2 i64) (result i64)
    (local $l3 i32) (local $l4 i64) (local $l5 i64) (local $l6 i64) (local $l7 i64) (local $l8 i64) (local $l9 i64) (local $l10 i64) (local $l11 i64) (local $l12 i64) (local $l13 i64) (local $l14 i32)
    global.get $__stack_pointer
    i32.const 240
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    i32.const 168
    i32.add
    local.get $p0
    call $_ZN155_$LT$soroban_sdk..bytes..BytesN$LT$_$GT$$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h44db584ecfeb8fbeE
    block  ;; label = @1
      local.get $l3
      i32.load offset=168
      br_if 0 (;@1;)
      local.get $p1
      i64.const 255
      i64.and
      i64.const 75
      i64.ne
      br_if 0 (;@1;)
      local.get $p2
      i64.const 255
      i64.and
      i64.const 75
      i64.ne
      br_if 0 (;@1;)
      local.get $l3
      i64.load offset=176
      local.set $l4
      local.get $p1
      call $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE
      i64.const 32
      i64.shr_u
      local.set $l5
      i64.const -4294967292
      local.set $l6
      i64.const 0
      local.set $p0
      loop  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              block  ;; label = @6
                block  ;; label = @7
                  local.get $l5
                  local.get $p0
                  i64.eq
                  br_if 0 (;@7;)
                  local.get $l3
                  i32.const 200
                  i32.add
                  local.get $p1
                  local.get $l6
                  i64.const 4294967296
                  i64.add
                  local.tee $l7
                  call $_ZN17soroban_env_guest5guest3vec7vec_get17he3c7204fed333c8fE
                  call $_ZN158_$LT$soroban_account_contract..AccSignature$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h81ea9020b451ff5bE
                  local.get $l3
                  i64.load offset=200
                  i64.eqz
                  i32.eqz
                  br_if 6 (;@1;)
                  local.get $l3
                  i64.load offset=216
                  local.set $l8
                  local.get $l3
                  i64.load offset=208
                  local.set $l9
                  local.get $p0
                  i64.const 0
                  i64.eq
                  br_if 1 (;@6;)
                  local.get $l3
                  i32.const 200
                  i32.add
                  local.get $p1
                  local.get $l6
                  call $_ZN17soroban_env_guest5guest3vec7vec_get17he3c7204fed333c8fE
                  call $_ZN158_$LT$soroban_account_contract..AccSignature$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h81ea9020b451ff5bE
                  local.get $l3
                  i64.load offset=200
                  i64.eqz
                  i32.eqz
                  br_if 6 (;@1;)
                  local.get $l3
                  i64.load offset=208
                  local.get $l9
                  call $_ZN17soroban_env_guest5guest7context7obj_cmp17h189bc77d88b5cf98E
                  i64.const -1
                  i64.le_s
                  br_if 1 (;@6;)
                  i64.const 12884901888
                  local.set $l5
                  br 2 (;@5;)
                end
                block  ;; label = @7
                  block  ;; label = @8
                    i64.const 0
                    local.get $p0
                    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h1f50ce4880217dc2E
                    local.tee $p0
                    call $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE
                    i32.eqz
                    br_if 0 (;@8;)
                    local.get $p0
                    call $_ZN11soroban_sdk7storage7Storage12get_internal17h7f02af1cc2480626E
                    local.tee $p0
                    i64.const 255
                    i64.and
                    i64.const 4
                    i64.ne
                    br_if 7 (;@1;)
                    local.get $p1
                    call $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE
                    local.get $p0
                    i64.xor
                    local.set $l10
                    call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h145672d3b76b8d44E
                    local.set $l11
                    call $_ZN17soroban_env_guest5guest3map7map_new17h81a78b249b2dc082E
                    local.set $l8
                    local.get $p2
                    call $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE
                    i64.const 32
                    i64.shr_u
                    local.set $l12
                    i64.const 2
                    local.set $l13
                    i64.const 0
                    local.set $p0
                    block  ;; label = @9
                      loop  ;; label = @10
                        local.get $p0
                        local.get $l12
                        i64.ge_u
                        br_if 6 (;@4;)
                        i64.const 2
                        local.set $l6
                        block  ;; label = @11
                          block  ;; label = @12
                            local.get $p2
                            local.get $p0
                            i64.const 32
                            i64.shl
                            i64.const 4
                            i64.or
                            call $_ZN17soroban_env_guest5guest3vec7vec_get17he3c7204fed333c8fE
                            local.tee $l9
                            i64.const 255
                            i64.and
                            i64.const 75
                            i64.ne
                            br_if 0 (;@12;)
                            local.get $l9
                            call $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE
                            local.set $l7
                            local.get $l3
                            i32.const 0
                            i32.store offset=192
                            local.get $l3
                            local.get $l9
                            i64.store offset=184
                            local.get $l3
                            local.get $l7
                            i64.const 32
                            i64.shr_u
                            i64.store32 offset=196
                            local.get $l3
                            i32.const 152
                            i32.add
                            local.get $l3
                            i32.const 184
                            i32.add
                            call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E
                            local.get $l3
                            i64.load offset=152
                            i32.wrap_i64
                            br_if 0 (;@12;)
                            local.get $l3
                            i32.const 136
                            i32.add
                            local.get $l3
                            i64.load offset=160
                            call $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0ee459b69aad7985E
                            local.get $l3
                            i64.load offset=136
                            i32.wrap_i64
                            br_if 0 (;@12;)
                            block  ;; label = @13
                              block  ;; label = @14
                                block  ;; label = @15
                                  local.get $l3
                                  i64.load offset=144
                                  i32.const 1048596
                                  i32.const 2
                                  call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$20symbol_index_in_strs17h3d41eba480718a90E
                                  i64.const 32
                                  i64.shr_u
                                  i32.wrap_i64
                                  br_table 0 (;@15;) 1 (;@14;) 3 (;@12;)
                                end
                                local.get $l3
                                i32.load offset=192
                                local.get $l3
                                i32.load offset=196
                                call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
                                i32.const 1
                                i32.le_u
                                br_if 1 (;@13;)
                                br 2 (;@12;)
                              end
                              local.get $l3
                              i32.load offset=192
                              local.get $l3
                              i32.load offset=196
                              call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
                              i32.const 1
                              i32.gt_u
                              br_if 1 (;@12;)
                              local.get $l3
                              i32.const 120
                              i32.add
                              local.get $l3
                              i32.const 184
                              i32.add
                              call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E
                              local.get $l3
                              i64.load offset=120
                              i32.wrap_i64
                              br_if 1 (;@12;)
                              local.get $l3
                              i64.load offset=128
                              local.set $l9
                              i32.const 0
                              local.set $l14
                              block  ;; label = @14
                                loop  ;; label = @15
                                  local.get $l14
                                  i32.const 16
                                  i32.eq
                                  br_if 1 (;@14;)
                                  local.get $l3
                                  i32.const 224
                                  i32.add
                                  local.get $l14
                                  i32.add
                                  i64.const 2
                                  i64.store
                                  local.get $l14
                                  i32.const 8
                                  i32.add
                                  local.set $l14
                                  br 0 (;@15;)
                                end
                              end
                              local.get $l9
                              i64.const 255
                              i64.and
                              i64.const 76
                              i64.ne
                              br_if 1 (;@12;)
                              local.get $l9
                              i32.const 1049296
                              i32.const 2
                              local.get $l3
                              i32.const 224
                              i32.add
                              i32.const 2
                              call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h8a577be1f73f732bE
                              local.get $l3
                              i64.load offset=224
                              local.tee $l9
                              i64.const 255
                              i64.and
                              i64.const 75
                              i64.ne
                              br_if 1 (;@12;)
                              local.get $l9
                              call $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE
                              local.set $l7
                              local.get $l3
                              i32.const 0
                              i32.store offset=208
                              local.get $l3
                              local.get $l9
                              i64.store offset=200
                              local.get $l3
                              local.get $l7
                              i64.const 32
                              i64.shr_u
                              i64.store32 offset=212
                              local.get $l3
                              i32.const 104
                              i32.add
                              local.get $l3
                              i32.const 200
                              i32.add
                              call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E
                              local.get $l3
                              i64.load offset=104
                              i32.wrap_i64
                              br_if 1 (;@12;)
                              local.get $l3
                              i32.const 88
                              i32.add
                              local.get $l3
                              i64.load offset=112
                              call $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0ee459b69aad7985E
                              local.get $l3
                              i64.load offset=88
                              i32.wrap_i64
                              br_if 1 (;@12;)
                              local.get $l3
                              i64.load offset=96
                              i32.const 1049316
                              i32.const 1
                              call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$20symbol_index_in_strs17h3d41eba480718a90E
                              i64.const 4294967295
                              i64.gt_u
                              br_if 1 (;@12;)
                              local.get $l3
                              i32.load offset=208
                              local.get $l3
                              i32.load offset=212
                              call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
                              i32.const 1
                              i32.gt_u
                              br_if 1 (;@12;)
                              local.get $l3
                              i32.const 72
                              i32.add
                              local.get $l3
                              i32.const 200
                              i32.add
                              call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E
                              local.get $l3
                              i64.load offset=72
                              i32.wrap_i64
                              br_if 1 (;@12;)
                              local.get $l3
                              i32.const 56
                              i32.add
                              local.get $l3
                              i64.load offset=80
                              call $_ZN155_$LT$soroban_sdk..bytes..BytesN$LT$_$GT$$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h44db584ecfeb8fbeE
                              local.get $l3
                              i64.load offset=56
                              i32.wrap_i64
                              br_if 1 (;@12;)
                              local.get $l3
                              i64.load offset=64
                              local.set $l9
                              local.get $l3
                              i32.const 40
                              i32.add
                              local.get $l3
                              i64.load offset=232
                              call $_ZN155_$LT$soroban_sdk..bytes..BytesN$LT$_$GT$$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h44db584ecfeb8fbeE
                              local.get $l3
                              i64.load offset=40
                              i32.wrap_i64
                              br_if 1 (;@12;)
                              local.get $l3
                              i64.load offset=48
                              local.set $l7
                              i64.const 1
                              local.set $l6
                              br 2 (;@11;)
                            end
                            local.get $l3
                            i32.const 24
                            i32.add
                            local.get $l3
                            i32.const 184
                            i32.add
                            call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E
                            local.get $l3
                            i64.load offset=24
                            i32.wrap_i64
                            br_if 0 (;@12;)
                            local.get $l3
                            i64.load offset=32
                            local.set $l9
                            i32.const 0
                            local.set $l14
                            block  ;; label = @13
                              loop  ;; label = @14
                                local.get $l14
                                i32.const 24
                                i32.eq
                                br_if 1 (;@13;)
                                local.get $l3
                                i32.const 200
                                i32.add
                                local.get $l14
                                i32.add
                                i64.const 2
                                i64.store
                                local.get $l14
                                i32.const 8
                                i32.add
                                local.set $l14
                                br 0 (;@14;)
                              end
                            end
                            local.get $l9
                            i64.const 255
                            i64.and
                            i64.const 76
                            i64.ne
                            br_if 0 (;@12;)
                            local.get $l9
                            i32.const 1049256
                            i32.const 3
                            local.get $l3
                            i32.const 200
                            i32.add
                            i32.const 3
                            call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h8a577be1f73f732bE
                            local.get $l3
                            i64.load offset=200
                            local.tee $p1
                            i64.const 255
                            i64.and
                            i64.const 75
                            i64.ne
                            br_if 0 (;@12;)
                            local.get $l3
                            i64.load offset=208
                            local.tee $l9
                            i64.const 255
                            i64.and
                            i64.const 77
                            i64.ne
                            br_if 0 (;@12;)
                            local.get $l3
                            i32.const 8
                            i32.add
                            local.get $l3
                            i64.load offset=216
                            call $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0ee459b69aad7985E
                            local.get $l3
                            i64.load offset=8
                            i32.wrap_i64
                            br_if 0 (;@12;)
                            local.get $l3
                            i64.load offset=16
                            local.set $l7
                            i64.const 0
                            local.set $l6
                            br 1 (;@11;)
                          end
                        end
                        block  ;; label = @11
                          local.get $p0
                          i64.const 4294967295
                          i64.eq
                          br_if 0 (;@11;)
                          local.get $l6
                          i64.const 2
                          i64.eq
                          br_if 2 (;@9;)
                          block  ;; label = @12
                            local.get $l6
                            i64.const 0
                            i64.eq
                            br_if 0 (;@12;)
                            i64.const 21474836480
                            local.set $l5
                            br 7 (;@5;)
                          end
                          i64.const 4294967296
                          local.set $l5
                          local.get $l9
                          local.get $l11
                          call $_ZN17soroban_env_guest5guest7context7obj_cmp17h189bc77d88b5cf98E
                          local.set $l6
                          block  ;; label = @12
                            local.get $l10
                            i64.const 4294967296
                            i64.lt_u
                            br_if 0 (;@12;)
                            local.get $l6
                            i64.eqz
                            br_if 7 (;@5;)
                          end
                          block  ;; label = @12
                            block  ;; label = @13
                              local.get $l7
                              i64.const 65154533130155790
                              call $_ZN4core3cmp9PartialEq2ne17hdc583e0bce855b48E
                              i32.eqz
                              br_if 0 (;@13;)
                              local.get $l7
                              i32.const 1048659
                              i32.const 7
                              call $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17h1647bdd1d3a8fa36E
                              call $_ZN4core3cmp9PartialEq2ne17hdc583e0bce855b48E
                              br_if 1 (;@12;)
                            end
                            block  ;; label = @13
                              block  ;; label = @14
                                local.get $l8
                                local.get $l9
                                call $_ZN17soroban_env_guest5guest3map7map_has17hc11ce5fcb08aa3f6E
                                i64.const 1
                                i64.ne
                                br_if 0 (;@14;)
                                local.get $l3
                                i32.const 200
                                i32.add
                                local.get $l8
                                local.get $l9
                                call $_ZN17soroban_env_guest5guest3map7map_get17hfaa762dc2cd709cbE
                                call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
                                local.get $l3
                                i64.load offset=200
                                i64.const 0
                                i64.ne
                                br_if 13 (;@1;)
                                local.get $l3
                                i32.const 200
                                i32.add
                                i32.const 16
                                i32.add
                                i64.load
                                local.set $l6
                                br 1 (;@13;)
                              end
                              i64.const 2
                              local.get $l9
                              call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h1f50ce4880217dc2E
                              local.tee $l6
                              call $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE
                              i32.eqz
                              br_if 1 (;@12;)
                              local.get $l3
                              i32.const 200
                              i32.add
                              local.get $l6
                              call $_ZN11soroban_sdk7storage7Storage12get_internal17h7f02af1cc2480626E
                              call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
                              local.get $l3
                              i64.load offset=200
                              i64.eqz
                              i32.eqz
                              br_if 12 (;@1;)
                              local.get $l3
                              i32.const 200
                              i32.add
                              i32.const 16
                              i32.add
                              i64.load
                              local.set $l6
                            end
                            local.get $l3
                            i64.load offset=208
                            local.set $l4
                            local.get $p1
                            call $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE
                            i64.const 32
                            i64.shr_u
                            i32.wrap_i64
                            i32.const 2
                            i32.le_u
                            br_if 4 (;@8;)
                            local.get $l3
                            i32.const 200
                            i32.add
                            local.get $p1
                            i64.const 8589934596
                            call $_ZN17soroban_env_guest5guest3vec7vec_get17he3c7204fed333c8fE
                            call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
                            local.get $l3
                            i64.load offset=200
                            i64.eqz
                            i32.eqz
                            br_if 5 (;@7;)
                            block  ;; label = @13
                              local.get $l3
                              i32.const 200
                              i32.add
                              i32.const 16
                              i32.add
                              i64.load
                              local.tee $l7
                              i64.const 0
                              i64.ge_s
                              br_if 0 (;@13;)
                              i64.const 8589934592
                              local.set $l5
                              br 8 (;@5;)
                            end
                            local.get $l3
                            i64.load offset=208
                            local.set $p1
                            i64.const 4294967296
                            local.set $l5
                            block  ;; label = @13
                              local.get $l10
                              i64.const 4294967296
                              i64.lt_u
                              br_if 0 (;@13;)
                              local.get $p1
                              local.get $l4
                              i64.gt_u
                              local.get $l7
                              local.get $l6
                              i64.gt_s
                              local.get $l7
                              local.get $l6
                              i64.eq
                              select
                              br_if 8 (;@5;)
                            end
                            local.get $l6
                            local.get $l7
                            i64.xor
                            local.get $l6
                            local.get $l6
                            local.get $l7
                            i64.sub
                            local.get $l4
                            local.get $p1
                            i64.lt_u
                            i64.extend_i32_u
                            i64.sub
                            local.tee $l7
                            i64.xor
                            i64.and
                            i64.const 0
                            i64.lt_s
                            br_if 1 (;@11;)
                            local.get $l8
                            local.get $l9
                            local.get $l4
                            local.get $p1
                            i64.sub
                            local.get $l7
                            call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17he61e6e8b3f136369E
                            call $_ZN17soroban_env_guest5guest3map7map_put17h27b18abb0ba80dc7E
                            local.set $l8
                          end
                          local.get $p0
                          i64.const 1
                          i64.add
                          local.set $p0
                          br 1 (;@10;)
                        end
                      end
                      call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
                      unreachable
                    end
                    local.get $l3
                    i32.const 184
                    i32.add
                    i32.const 1048612
                    call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
                    unreachable
                  end
                  call $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E
                  unreachable
                end
                local.get $l3
                i32.const 224
                i32.add
                i32.const 1048628
                call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
                unreachable
              end
              i64.const 1
              local.get $l9
              call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h1f50ce4880217dc2E
              call $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE
              br_if 2 (;@3;)
              i64.const 17179869184
              local.set $l5
            end
            local.get $l5
            i64.const 30064771072
            i64.and
            i64.const 3
            i64.or
            local.set $l13
          end
          local.get $l3
          i32.const 240
          i32.add
          global.set $__stack_pointer
          local.get $l13
          return
        end
        local.get $l9
        local.get $l4
        local.get $l8
        call $_ZN17soroban_env_guest5guest6crypto18verify_sig_ed2551917hb3129d31d3626aacE
        drop
        local.get $p0
        i64.const 1
        i64.add
        local.set $p0
        local.get $l7
        local.set $l6
        br 0 (;@2;)
      end
    end
    unreachable
    unreachable)
  (func $_ZN11soroban_sdk7storage7Storage12has_internal17h1a0464cd8b05ca6fE (type $t15) (param $p0 i64) (result i32)
    local.get $p0
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE
    i64.const 1
    i64.eq)
  (func $_ZN11soroban_sdk7storage7Storage12get_internal17h7f02af1cc2480626E (type $t3) (param $p0 i64) (result i64)
    local.get $p0
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E)
  (func $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E (type $t14) (param $p0 i32) (param $p1 i32)
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
      i64.load
      local.get $l2
      i64.extend_i32_u
      i64.const 32
      i64.shl
      i64.const 4
      i64.or
      call $_ZN17soroban_env_guest5guest3vec7vec_get17he3c7204fed333c8fE
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
  (func $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0ee459b69aad7985E (type $t10) (param $p0 i32) (param $p1 i64)
    (local $l2 i32)
    local.get $p0
    local.get $p1
    i64.store offset=8
    local.get $p0
    local.get $p1
    i32.wrap_i64
    i32.const 255
    i32.and
    local.tee $l2
    i32.const 14
    i32.ne
    local.get $l2
    i32.const 74
    i32.ne
    i32.and
    i64.extend_i32_u
    i64.store)
  (func $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$20symbol_index_in_strs17h3d41eba480718a90E (type $t16) (param $p0 i64) (param $p1 i32) (param $p2 i32) (result i64)
    local.get $p0
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
    call $_ZN17soroban_env_guest5guest3buf29symbol_index_in_linear_memory17hbc21e0d3e948fc5aE)
  (func $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
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
    call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
    unreachable)
  (func $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E (type $t13)
    call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
    unreachable)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t13)
    unreachable
    unreachable)
  (func $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E (type $t17) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (result i32)
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
          call_indirect $T0 (type $t1)
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
  (func $_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i32$GT$3fmt17hd6308d8453dcc3baE (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
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
        i32.const 1048729
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
        i32.const 1048729
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
      i32.const 1048729
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
        i32.const 1048729
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
        call_indirect $T0 (type $t0)
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
        call_indirect $T0 (type $t0)
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
            call_indirect $T0 (type $t1)
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
        call_indirect $T0 (type $t0)
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
          call_indirect $T0 (type $t1)
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
      call_indirect $T0 (type $t0)
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
        call_indirect $T0 (type $t1)
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
  (func $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17hb37de2cca199de8bE (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p1
    local.get $p0
    i32.load
    local.get $p0
    i32.load offset=4
    call $_ZN4core3fmt9Formatter3pad17hdad3e25ba05328b0E)
  (func $_ZN69_$LT$soroban_env_common..error..Error$u20$as$u20$core..fmt..Debug$GT$3fmt17h2f2be93d53eefd32E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
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
              i32.const 1049128
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
            i32.const 1049156
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
          i32.const 1049212
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
        i32.const 1049156
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
      i32.const 1049188
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
  (func $_ZN11stellar_xdr4curr9generated11ScErrorType4name17h419699d3f4325e34E (type $t14) (param $p0 i32) (param $p1 i32)
    local.get $p0
    local.get $p1
    i32.const 2
    i32.shl
    local.tee $p1
    i32.const 1049324
    i32.add
    i32.load
    i32.store offset=4
    local.get $p0
    local.get $p1
    i32.const 1049364
    i32.add
    i32.load
    i32.store)
  (func $_ZN11stellar_xdr4curr9generated11ScErrorCode4name17h04c17a0e8b1b13b8E (type $t14) (param $p0 i32) (param $p1 i32)
    local.get $p0
    local.get $p1
    i32.const 2
    i32.shl
    local.tee $p1
    i32.const 1049404
    i32.add
    i32.load
    i32.store offset=4
    local.get $p0
    local.get $p1
    i32.const 1049444
    i32.add
    i32.load
    i32.store)
  (func $_ZN4core3fmt9Formatter9write_fmt17hdb78605d5d178ddcE (type $t0) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
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
                  call_indirect $T0 (type $t0)
                  br_if 4 (;@3;)
                end
                local.get $p2
                i32.load
                local.get $l3
                i32.const 12
                i32.add
                local.get $p2
                i32.load offset=4
                call_indirect $T0 (type $t1)
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
                call_indirect $T0 (type $t0)
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
              call_indirect $T0 (type $t1)
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
          call_indirect $T0 (type $t0)
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
  (func $_ (type $t13))
  (table $T0 5 5 funcref)
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1049484))
  (global $__heap_base i32 (i32.const 1049488))
  (export "memory" (memory $memory))
  (export "init" (func $init))
  (export "add_limit" (func $add_limit))
  (export "__check_auth" (func $__check_auth))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (elem $e0 (i32.const 1) func $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17hb37de2cca199de8bE $_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i32$GT$3fmt17hd6308d8453dcc3baE $_ZN77_$LT$soroban_env_common..val..ConversionError$u20$as$u20$core..fmt..Debug$GT$3fmt17hd509f52596321fbfE $_ZN69_$LT$soroban_env_common..error..Error$u20$as$u20$core..fmt..Debug$GT$3fmt17h2f2be93d53eefd32E)
  (data $.rodata (i32.const 1048576) "CreateContractHostFn\df\01\10\00\08\00\00\00\00\00\10\00\14\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\03\00\00\00\00\00\00\00\08\00\00\00\08\00\00\00\04\00\00\00ConversionErrorapprovepublic_keysignature\00\00\00Z\00\10\00\0a\00\00\00d\00\10\00\09\00\00\00SignerCntSignerSpendLimit00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899ArithDomainIndexBoundsInvalidInputMissingValueExistingValueExceededLimitInvalidActionInternalErrorUnexpectedTypeUnexpectedSizeContractWasmVmContextStorageObjectCryptoEventsBudgetValueAuthError(, )\00\00\00\1c\02\10\00\06\00\00\00\22\02\10\00\02\00\00\00$\02\10\00\01\00\00\00, #\00\1c\02\10\00\06\00\00\00@\02\10\00\03\00\00\00$\02\10\00\01\00\00\00Error(#\00\5c\02\10\00\07\00\00\00\22\02\10\00\02\00\00\00$\02\10\00\01\00\00\00\5c\02\10\00\07\00\00\00@\02\10\00\03\00\00\00$\02\10\00\01\00\00\00argscontractfn_name\00\94\02\10\00\04\00\00\00\98\02\10\00\08\00\00\00\a0\02\10\00\07\00\00\00executablesalt\00\00\c0\02\10\00\0a\00\00\00\ca\02\10\00\04\00\00\00Wasm\e0\02\10\00\04\00\00\00\08\00\00\00\06\00\00\00\07\00\00\00\07\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\06\00\00\00\05\00\00\00\04\00\00\00\df\01\10\00\e7\01\10\00\ed\01\10\00\f4\01\10\00\fb\01\10\00\01\02\10\00\07\02\10\00\0d\02\10\00\13\02\10\00\18\02\10\00\0b\00\00\00\0b\00\00\00\0c\00\00\00\0c\00\00\00\0d\00\00\00\0d\00\00\00\0d\00\00\00\0d\00\00\00\0e\00\00\00\0e\00\00\00a\01\10\00l\01\10\00w\01\10\00\83\01\10\00\8f\01\10\00\9c\01\10\00\a9\01\10\00\b6\01\10\00\c3\01\10\00\d1\01\10\00"))
