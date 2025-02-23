(module $soroban_other_custom_types_contract.wasm
  (type $t0 (func (param i64 i64) (result i64)))
  (type $t1 (func (param i64) (result i64)))
  (type $t2 (func (param i64 i64 i64 i64) (result i64)))
  (type $t3 (func (param i64 i64 i64) (result i64)))
  (type $t4 (func (param i32)))
  (type $t5 (func (param i32) (result i64)))
  (type $t6 (func (param i32 i32) (result i64)))
  (type $t7 (func (param i32 i64)))
  (type $t8 (func (param i64) (result i32)))
  (type $t9 (func (param i32 i32)))
  (type $t10 (func (param i64 i32 i32) (result i64)))
  (type $t11 (func (param i32 i32) (result i32)))
  (type $t12 (func (result i64)))
  (type $t13 (func))
  (type $t14 (func (param i64 i32)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE (type $t0)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E (type $t0)))
  (import "v" "3" (func $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE (type $t1)))
  (import "m" "a" (func $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h15a7786289874722E (type $t2)))
  (import "m" "9" (func $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17h999916ef23111b0dE (type $t3)))
  (import "a" "0" (func $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE (type $t1)))
  (import "b" "i" (func $_ZN17soroban_env_guest5guest3buf29string_new_from_linear_memory17h2ece9a81b6f0b712E (type $t0)))
  (import "x" "1" (func $_ZN17soroban_env_guest5guest7context14contract_event17h9ea3fb3010f39aa8E (type $t0)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E (type $t3)))
  (import "i" "2" (func $_ZN17soroban_env_guest5guest3int10obj_to_i6417h376f6985bfbe3666E (type $t1)))
  (import "i" "1" (func $_ZN17soroban_env_guest5guest3int12obj_from_i6417h668746a0b5b3522cE (type $t1)))
  (import "b" "8" (func $_ZN17soroban_env_guest5guest3buf9bytes_len17h783b00115bb1ca2bE (type $t1)))
  (import "i" "5" (func $_ZN17soroban_env_guest5guest3int16obj_to_u128_hi6417hc25fd70bb9d05601E (type $t1)))
  (import "i" "4" (func $_ZN17soroban_env_guest5guest3int16obj_to_u128_lo6417he43d5142d6a48897E (type $t1)))
  (import "i" "3" (func $_ZN17soroban_env_guest5guest3int20obj_from_u128_pieces17h4acfa69b076bf872E (type $t0)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE (type $t0)))
  (import "i" "8" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_hi6417h96047db195ed49dfE (type $t1)))
  (import "i" "7" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_lo6417hda737eee8cb86207E (type $t1)))
  (import "i" "6" (func $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17ha9df624d96cf2a1dE (type $t0)))
  (import "v" "1" (func $_ZN17soroban_env_guest5guest3vec7vec_get17he3c7204fed333c8fE (type $t0)))
  (import "b" "j" (func $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h65f4c5e4b5b0b386E (type $t0)))
  (import "v" "h" (func $_ZN17soroban_env_guest5guest3vec27vec_unpack_to_linear_memory17hbb96611dc359fde3E (type $t3)))
  (import "b" "m" (func $_ZN17soroban_env_guest5guest3buf29symbol_index_in_linear_memory17hbc21e0d3e948fc5aE (type $t3)))
  (func $_ZN11soroban_sdk7storage10Persistent3get17h625919ee72b9a9a3E (type $t4) (param $p0 i32)
    (local $l1 i32) (local $l2 i64) (local $l3 i32)
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          i64.const 253576579652878
          i64.const 1
          call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE
          i64.const 1
          i64.eq
          br_if 0 (;@3;)
          i32.const 0
          local.set $l1
          br 1 (;@2;)
        end
        i64.const 253576579652878
        i64.const 1
        call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E
        local.tee $l2
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 1 (;@1;)
        local.get $l2
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        local.set $l3
        i32.const 1
        local.set $l1
      end
      local.get $p0
      local.get $l3
      i32.store offset=4
      local.get $p0
      local.get $l1
      i32.store
      return
    end
    unreachable
    unreachable)
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h57035ce1931bf2f3E (type $t5) (param $p0 i32) (result i64)
    (local $l1 i32) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            local.get $p0
            i32.const 255
            i32.and
            br_table 0 (;@4;) 1 (;@3;) 2 (;@2;) 0 (;@4;)
          end
          i32.const 1048604
          i32.const 5
          call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
          local.set $l2
          br 2 (;@1;)
        end
        i32.const 1048609
        i32.const 6
        call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
        local.set $l2
        br 1 (;@1;)
      end
      i32.const 1048615
      i32.const 5
      call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
      local.set $l2
    end
    local.get $l1
    local.get $l2
    call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hac49a8775e940f98E
    local.get $l1
    i64.load offset=8
    local.set $l2
    local.get $l1
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l2)
  (func $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE (type $t6) (param $p0 i32) (param $p1 i32) (result i64)
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
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hac49a8775e940f98E (type $t7) (param $p0 i32) (param $p1 i64)
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
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h78558b51b19f7364E (type $t8) (param $p0 i64) (result i32)
    (local $l1 i32) (local $l2 i32) (local $l3 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    i32.const 3
    local.set $l2
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 75
      i64.ne
      br_if 0 (;@1;)
      local.get $p0
      call $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE
      local.set $l3
      local.get $l1
      i32.const 0
      i32.store offset=40
      local.get $l1
      local.get $p0
      i64.store offset=32
      local.get $l1
      local.get $l3
      i64.const 32
      i64.shr_u
      i64.store32 offset=44
      local.get $l1
      i32.const 16
      i32.add
      local.get $l1
      i32.const 32
      i32.add
      call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E
      local.get $l1
      i64.load offset=16
      i32.wrap_i64
      br_if 0 (;@1;)
      local.get $l1
      local.get $l1
      i64.load offset=24
      call $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0ee459b69aad7985E
      local.get $l1
      i64.load
      i32.wrap_i64
      br_if 0 (;@1;)
      i32.const 3
      local.set $l2
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            local.get $l1
            i64.load offset=8
            i32.const 1048620
            i32.const 3
            call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$20symbol_index_in_strs17hbcbd3fba7074b460E
            i64.const 32
            i64.shr_u
            i32.wrap_i64
            br_table 0 (;@4;) 1 (;@3;) 2 (;@2;) 3 (;@1;)
          end
          local.get $l1
          i32.load offset=40
          local.get $l1
          i32.load offset=44
          call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
          br_if 2 (;@1;)
          i32.const 0
          local.set $l2
          br 2 (;@1;)
        end
        local.get $l1
        i32.load offset=40
        local.get $l1
        i32.load offset=44
        call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
        br_if 1 (;@1;)
        i32.const 1
        local.set $l2
        br 1 (;@1;)
      end
      local.get $l1
      i32.load offset=40
      local.get $l1
      i32.load offset=44
      call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
      br_if 0 (;@1;)
      i32.const 2
      local.set $l2
    end
    local.get $l1
    i32.const 48
    i32.add
    global.set $__stack_pointer
    local.get $l2)
  (func $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E (type $t9) (param $p0 i32) (param $p1 i32)
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
  (func $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0ee459b69aad7985E (type $t7) (param $p0 i32) (param $p1 i64)
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
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$20symbol_index_in_strs17hbcbd3fba7074b460E (type $t10) (param $p0 i64) (param $p1 i32) (param $p2 i32) (result i64)
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
  (func $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E (type $t11) (param $p0 i32) (param $p1 i32) (result i32)
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
  (func $_ZN161_$LT$soroban_other_custom_types_contract..Test$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hfd3dae653f8c60a6E (type $t7) (param $p0 i32) (param $p1 i64)
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
        i32.const 24
        i32.eq
        br_if 1 (;@1;)
        local.get $l2
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
            local.get $p1
            i32.const 1048580
            i64.extend_i32_u
            i64.const 32
            i64.shl
            i64.const 4
            i64.or
            local.get $l2
            i32.const 24
            i32.add
            i64.extend_i32_u
            i64.const 32
            i64.shl
            i64.const 4
            i64.or
            i64.const 12884901892
            call $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17h15a7786289874722E
            drop
            local.get $l2
            i64.load offset=24
            local.tee $p1
            i64.const 255
            i64.and
            i64.const 4
            i64.ne
            br_if 1 (;@3;)
            i32.const 1
            local.get $l2
            i32.load8_u offset=32
            local.tee $l3
            i32.const 0
            i32.ne
            i32.const 1
            i32.shl
            local.get $l3
            i32.const 1
            i32.eq
            select
            local.tee $l3
            i32.const 2
            i32.eq
            br_if 2 (;@2;)
            local.get $l2
            i32.const 8
            i32.add
            local.get $l2
            i64.load offset=40
            call $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0ee459b69aad7985E
            block  ;; label = @5
              local.get $l2
              i64.load offset=8
              i32.wrap_i64
              br_if 0 (;@5;)
              local.get $l2
              i64.load offset=16
              local.set $l4
              local.get $p0
              local.get $l3
              i32.const 1
              i32.and
              i32.store8 offset=12
              local.get $p0
              local.get $p1
              i64.const 32
              i64.shr_u
              i32.wrap_i64
              i32.store offset=8
              local.get $p0
              local.get $l4
              i64.store
              br 4 (;@1;)
            end
            local.get $p0
            i32.const 2
            i32.store8 offset=12
            br 3 (;@1;)
          end
          local.get $p0
          i32.const 2
          i32.store8 offset=12
          br 2 (;@1;)
        end
        local.get $p0
        i32.const 2
        i32.store8 offset=12
        br 1 (;@1;)
      end
      local.get $p0
      i32.const 2
      i32.store8 offset=12
    end
    local.get $l2
    i32.const 48
    i32.add
    global.set $__stack_pointer)
  (func $_ZN35soroban_other_custom_types_contract171_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_other_custom_types_contract..Test$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17hf4808d7c6a1e4682E (type $t5) (param $p0 i32) (result i64)
    (local $l1 i32) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    local.get $p0
    i64.load
    i64.store offset=24
    local.get $l1
    local.get $p0
    i64.load8_u offset=12
    i64.store offset=16
    local.get $l1
    local.get $p0
    i64.load32_u offset=8
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.store offset=8
    i32.const 1048580
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
    i64.const 12884901892
    call $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17h999916ef23111b0dE
    local.set $l2
    local.get $l1
    i32.const 32
    i32.add
    global.set $__stack_pointer
    local.get $l2)
  (func $hello (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    local.get $p0
    call $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0ee459b69aad7985E
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
    local.get $l1
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $p0)
  (func $auth (type $t0) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32) (local $l3 i64) (local $l4 i64) (local $l5 i32)
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
      call $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0ee459b69aad7985E
      local.get $l2
      i64.load
      i32.wrap_i64
      br_if 0 (;@1;)
      local.get $l2
      i64.load offset=8
      local.set $l3
      local.get $p0
      call $_ZN17soroban_env_guest5guest7address12require_auth17h998ebdb7158ed55dE
      drop
      local.get $l2
      i32.const 1048708
      i64.extend_i32_u
      i64.const 32
      i64.shl
      i64.const 4
      i64.or
      i64.const 17179869188
      call $_ZN17soroban_env_guest5guest3buf29string_new_from_linear_memory17h2ece9a81b6f0b712E
      local.tee $l4
      i64.store offset=16
      i64.const 2
      local.set $p1
      i32.const 1
      local.set $l5
      block  ;; label = @2
        loop  ;; label = @3
          local.get $l5
          i32.eqz
          br_if 1 (;@2;)
          local.get $l5
          i32.const -1
          i32.add
          local.set $l5
          local.get $l4
          local.set $p1
          br 0 (;@3;)
        end
      end
      local.get $l2
      local.get $p1
      i64.store offset=24
      local.get $l2
      i32.const 24
      i32.add
      i32.const 1
      call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E
      local.get $l3
      call $_ZN17soroban_env_guest5guest7context14contract_event17h9ea3fb3010f39aa8E
      drop
      local.get $l2
      i32.const 32
      i32.add
      global.set $__stack_pointer
      local.get $p0
      return
    end
    unreachable
    unreachable)
  (func $get_count (type $t12) (result i64)
    (local $l0 i32) (local $l1 i32) (local $l2 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    i32.const 8
    i32.add
    call $_ZN11soroban_sdk7storage10Persistent3get17h625919ee72b9a9a3E
    local.get $l0
    i32.load offset=8
    local.set $l1
    local.get $l0
    i32.load offset=12
    local.set $l2
    local.get $l0
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l2
    i32.const 0
    local.get $l1
    select
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or)
  (func $inc (type $t12) (result i64)
    (local $l0 i32) (local $l1 i32) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    i32.const 8
    i32.add
    call $_ZN11soroban_sdk7storage10Persistent3get17h625919ee72b9a9a3E
    block  ;; label = @1
      local.get $l0
      i32.load offset=12
      i32.const 0
      local.get $l0
      i32.load offset=8
      select
      i32.const 1
      i32.add
      local.tee $l1
      br_if 0 (;@1;)
      call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
      unreachable
    end
    i64.const 253576579652878
    local.get $l1
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    local.tee $l2
    i64.const 1
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E
    drop
    local.get $l0
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l2)
  (func $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E (type $t13)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $woid (type $t12) (result i64)
    i64.const 2)
  (func $val (type $t12) (result i64)
    i64.const 2)
  (func $u32_fail_on_even (type $t1) (param $p0 i64) (result i64)
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 4
      i64.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    i64.const 4294967299
    local.get $p0
    i64.const -4294967292
    i64.and
    local.get $p0
    i64.const 4294967296
    i64.and
    i64.eqz
    select)
  (func $u32_ (type $t1) (param $p0 i64) (result i64)
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 4
      i64.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0
    i64.const -4294967292
    i64.and)
  (func $i32_ (type $t1) (param $p0 i64) (result i64)
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 5
      i64.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0
    i64.const -4294967291
    i64.and)
  (func $i64_ (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i32.wrap_i64
        i32.const 255
        i32.and
        local.tee $l1
        i32.const 65
        i32.eq
        br_if 0 (;@2;)
        block  ;; label = @3
          local.get $l1
          i32.const 7
          i32.ne
          br_if 0 (;@3;)
          local.get $p0
          i64.const 8
          i64.shr_s
          local.set $p0
          br 2 (;@1;)
        end
        unreachable
        unreachable
      end
      local.get $p0
      call $_ZN17soroban_env_guest5guest3int10obj_to_i6417h376f6985bfbe3666E
      local.set $p0
    end
    block  ;; label = @1
      local.get $p0
      i64.const -36028797018963968
      i64.add
      i64.const -72057594037927936
      i64.lt_u
      br_if 0 (;@1;)
      local.get $p0
      i64.const 8
      i64.shl
      i64.const 7
      i64.or
      return
    end
    local.get $p0
    call $_ZN17soroban_env_guest5guest3int12obj_from_i6417h668746a0b5b3522cE)
  (func $strukt_hel (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    i32.const 16
    i32.add
    local.get $p0
    call $_ZN161_$LT$soroban_other_custom_types_contract..Test$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hfd3dae653f8c60a6E
    block  ;; label = @1
      local.get $l1
      i32.load8_u offset=28
      i32.const 2
      i32.eq
      br_if 0 (;@1;)
      local.get $l1
      local.get $l1
      i64.load offset=16
      i64.store offset=8
      local.get $l1
      i64.const 84475147278
      i64.store
      i32.const 0
      local.set $l2
      loop  ;; label = @2
        block  ;; label = @3
          local.get $l2
          i32.const 16
          i32.ne
          br_if 0 (;@3;)
          i32.const 0
          local.set $l2
          block  ;; label = @4
            loop  ;; label = @5
              local.get $l2
              i32.const 16
              i32.eq
              br_if 1 (;@4;)
              local.get $l1
              i32.const 16
              i32.add
              local.get $l2
              i32.add
              local.get $l1
              local.get $l2
              i32.add
              i64.load
              i64.store
              local.get $l2
              i32.const 8
              i32.add
              local.set $l2
              br 0 (;@5;)
            end
          end
          local.get $l1
          i32.const 16
          i32.add
          i32.const 2
          call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E
          local.set $p0
          local.get $l1
          i32.const 32
          i32.add
          global.set $__stack_pointer
          local.get $p0
          return
        end
        local.get $l1
        i32.const 16
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
    unreachable
    unreachable)
  (func $strukt (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    i32.const 16
    i32.add
    local.get $p0
    call $_ZN161_$LT$soroban_other_custom_types_contract..Test$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hfd3dae653f8c60a6E
    block  ;; label = @1
      local.get $l1
      i32.load8_u offset=28
      i32.const 2
      i32.ne
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $l1
    i32.const 8
    i32.add
    local.get $l1
    i32.const 16
    i32.add
    i32.const 8
    i32.add
    i64.load
    i64.store
    local.get $l1
    local.get $l1
    i64.load offset=16
    i64.store
    local.get $l1
    call $_ZN35soroban_other_custom_types_contract171_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_other_custom_types_contract..Test$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17hf4808d7c6a1e4682E
    local.set $p0
    local.get $l1
    i32.const 32
    i32.add
    global.set $__stack_pointer
    local.get $p0)
  (func $simple (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 64
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 75
      i64.ne
      br_if 0 (;@1;)
      local.get $p0
      call $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE
      local.set $l2
      local.get $l1
      i32.const 0
      i32.store offset=56
      local.get $l1
      local.get $p0
      i64.store offset=48
      local.get $l1
      local.get $l2
      i64.const 32
      i64.shr_u
      i64.store32 offset=60
      local.get $l1
      i32.const 32
      i32.add
      local.get $l1
      i32.const 48
      i32.add
      call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E
      local.get $l1
      i64.load offset=32
      i32.wrap_i64
      br_if 0 (;@1;)
      local.get $l1
      i32.const 16
      i32.add
      local.get $l1
      i64.load offset=40
      call $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0ee459b69aad7985E
      local.get $l1
      i64.load offset=16
      i32.wrap_i64
      br_if 0 (;@1;)
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              block  ;; label = @6
                local.get $l1
                i64.load offset=24
                i32.const 1048620
                i32.const 3
                call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$20symbol_index_in_strs17hbcbd3fba7074b460E
                i64.const 32
                i64.shr_u
                i32.wrap_i64
                br_table 1 (;@5;) 2 (;@4;) 0 (;@6;) 5 (;@1;)
              end
              local.get $l1
              i32.load offset=56
              local.get $l1
              i32.load offset=60
              call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
              i32.eqz
              br_if 2 (;@3;)
              br 4 (;@1;)
            end
            local.get $l1
            i32.load offset=56
            local.get $l1
            i32.load offset=60
            call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
            br_if 3 (;@1;)
            i32.const 1048604
            i32.const 5
            call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
            local.set $p0
            br 2 (;@2;)
          end
          local.get $l1
          i32.load offset=56
          local.get $l1
          i32.load offset=60
          call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
          br_if 2 (;@1;)
          i32.const 1048609
          i32.const 6
          call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
          local.set $p0
          br 1 (;@2;)
        end
        i32.const 1048615
        i32.const 5
        call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
        local.set $p0
      end
      local.get $l1
      local.get $p0
      call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hac49a8775e940f98E
      local.get $l1
      i64.load
      i32.wrap_i64
      br_if 0 (;@1;)
      local.get $l1
      i64.load offset=8
      local.set $p0
      local.get $l1
      i32.const 64
      i32.add
      global.set $__stack_pointer
      local.get $p0
      return
    end
    unreachable
    unreachable)
  (func $complex (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i64) (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32) (local $l7 i32) (local $l8 i64) (local $l9 i64)
    global.get $__stack_pointer
    i32.const 192
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 75
      i64.ne
      br_if 0 (;@1;)
      local.get $p0
      call $_ZN17soroban_env_guest5guest3vec7vec_len17h270553a501ca7facE
      local.set $l2
      local.get $l1
      i32.const 0
      i32.store offset=168
      local.get $l1
      local.get $p0
      i64.store offset=160
      local.get $l1
      local.get $l2
      i64.const 32
      i64.shr_u
      i64.store32 offset=172
      local.get $l1
      i32.const 112
      i32.add
      local.get $l1
      i32.const 160
      i32.add
      call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E
      local.get $l1
      i64.load offset=112
      i32.wrap_i64
      br_if 0 (;@1;)
      local.get $l1
      i32.const 96
      i32.add
      local.get $l1
      i64.load offset=120
      call $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0ee459b69aad7985E
      local.get $l1
      i64.load offset=96
      i32.wrap_i64
      br_if 0 (;@1;)
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              block  ;; label = @6
                block  ;; label = @7
                  local.get $l1
                  i64.load offset=104
                  i32.const 1048668
                  i32.const 5
                  call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$20symbol_index_in_strs17hbcbd3fba7074b460E
                  i64.const 32
                  i64.shr_u
                  i32.wrap_i64
                  br_table 0 (;@7;) 1 (;@6;) 2 (;@5;) 3 (;@4;) 4 (;@3;) 6 (;@1;)
                end
                local.get $l1
                i32.load offset=168
                local.get $l1
                i32.load offset=172
                call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
                i32.const 1
                i32.gt_u
                br_if 5 (;@1;)
                local.get $l1
                local.get $l1
                i32.const 160
                i32.add
                call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E
                local.get $l1
                i64.load
                i32.wrap_i64
                br_if 5 (;@1;)
                local.get $l1
                i32.const 128
                i32.add
                local.get $l1
                i64.load offset=8
                call $_ZN161_$LT$soroban_other_custom_types_contract..Test$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hfd3dae653f8c60a6E
                local.get $l1
                i32.load8_u offset=140
                i32.const 2
                i32.eq
                br_if 5 (;@1;)
                local.get $l1
                i64.load offset=136
                local.tee $p0
                i64.const 1095216660480
                i64.and
                i64.const 8589934592
                i64.eq
                br_if 5 (;@1;)
                local.get $l1
                i64.load offset=128
                local.set $l2
                local.get $l1
                i32.const 152
                i32.add
                i64.const 0
                i64.store
                local.get $l1
                local.get $p0
                i64.store offset=144
                local.get $l1
                local.get $l2
                i64.store offset=136
                local.get $l1
                i32.const 0
                i32.store8 offset=128
                i32.const 1048644
                i32.const 6
                call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
                local.get $l1
                i32.const 136
                i32.add
                call $_ZN35soroban_other_custom_types_contract171_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_other_custom_types_contract..Test$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17hf4808d7c6a1e4682E
                call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h5bb243f4c9a8fdcaE
                local.set $p0
                br 4 (;@2;)
              end
              local.get $l1
              i32.load offset=168
              local.get $l1
              i32.load offset=172
              call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
              i32.const 1
              i32.gt_u
              br_if 4 (;@1;)
              local.get $l1
              i32.const 16
              i32.add
              local.get $l1
              i32.const 160
              i32.add
              call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E
              local.get $l1
              i64.load offset=16
              local.tee $p0
              i64.const 2
              i64.eq
              br_if 4 (;@1;)
              local.get $p0
              i32.wrap_i64
              br_if 4 (;@1;)
              local.get $l1
              i64.load offset=24
              local.tee $p0
              i64.const 255
              i64.and
              i64.const 75
              i64.ne
              br_if 4 (;@1;)
              i32.const 0
              local.set $l3
              block  ;; label = @6
                loop  ;; label = @7
                  local.get $l3
                  i32.const 16
                  i32.eq
                  br_if 1 (;@6;)
                  local.get $l1
                  i32.const 176
                  i32.add
                  local.get $l3
                  i32.add
                  i64.const 2
                  i64.store
                  local.get $l3
                  i32.const 8
                  i32.add
                  local.set $l3
                  br 0 (;@7;)
                end
              end
              local.get $p0
              local.get $l1
              i32.const 176
              i32.add
              call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19vec_unpack_to_slice17h13b7b5195ebbe241E
              local.get $l1
              i32.const 128
              i32.add
              local.get $l1
              i64.load offset=176
              call $_ZN161_$LT$soroban_other_custom_types_contract..Test$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hfd3dae653f8c60a6E
              local.get $l1
              i32.load8_u offset=140
              local.tee $l4
              i32.const 2
              i32.eq
              br_if 4 (;@1;)
              local.get $l1
              i32.const 143
              i32.add
              i32.load8_u
              local.set $l5
              local.get $l1
              i32.load16_u offset=141 align=1
              local.set $l6
              local.get $l1
              i32.load offset=136
              local.set $l7
              local.get $l1
              i64.load offset=128
              local.set $p0
              local.get $l1
              i64.load offset=184
              call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h78558b51b19f7364E
              local.tee $l3
              i32.const 255
              i32.and
              i32.const 3
              i32.eq
              br_if 4 (;@1;)
              local.get $l1
              i32.const 152
              i32.add
              local.get $l3
              i64.extend_i32_u
              i64.const 255
              i64.and
              i64.store
              local.get $l1
              local.get $p0
              i64.store offset=136
              local.get $l1
              i32.const 1
              i32.store8 offset=128
              local.get $l1
              local.get $l6
              local.get $l5
              i32.const 16
              i32.shl
              i32.or
              i64.extend_i32_u
              i64.const 40
              i64.shl
              local.get $l7
              i64.extend_i32_u
              i64.or
              local.get $l4
              i64.extend_i32_u
              i64.const 32
              i64.shl
              i64.or
              i64.store offset=144
              i32.const 1048650
              i32.const 5
              call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
              local.set $p0
              local.get $l1
              i32.const 136
              i32.add
              call $_ZN35soroban_other_custom_types_contract171_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_other_custom_types_contract..Test$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17hf4808d7c6a1e4682E
              local.set $l2
              local.get $l1
              local.get $l3
              call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h57035ce1931bf2f3E
              i64.store offset=184
              local.get $l1
              local.get $l2
              i64.store offset=176
              local.get $p0
              local.get $l1
              i32.const 176
              i32.add
              i32.const 2
              call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E
              call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h5bb243f4c9a8fdcaE
              local.set $p0
              br 3 (;@2;)
            end
            local.get $l1
            i32.load offset=168
            local.get $l1
            i32.load offset=172
            call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
            i32.const 1
            i32.gt_u
            br_if 3 (;@1;)
            local.get $l1
            i32.const 32
            i32.add
            local.get $l1
            i32.const 160
            i32.add
            call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E
            local.get $l1
            i64.load offset=32
            i32.wrap_i64
            br_if 3 (;@1;)
            local.get $l1
            i64.load offset=40
            call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h78558b51b19f7364E
            local.tee $l3
            i32.const 255
            i32.and
            i32.const 3
            i32.eq
            br_if 3 (;@1;)
            i32.const 1048655
            i32.const 4
            call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
            local.get $l3
            call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h57035ce1931bf2f3E
            call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h5bb243f4c9a8fdcaE
            local.set $p0
            br 2 (;@2;)
          end
          local.get $l1
          i32.load offset=168
          local.get $l1
          i32.load offset=172
          call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
          i32.const 2
          i32.gt_u
          br_if 2 (;@1;)
          local.get $l1
          i32.const 64
          i32.add
          local.get $l1
          i32.const 160
          i32.add
          call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E
          local.get $l1
          i64.load offset=64
          i32.wrap_i64
          br_if 2 (;@1;)
          local.get $l1
          i64.load offset=72
          local.tee $p0
          i64.const 255
          i64.and
          i64.const 77
          i64.ne
          br_if 2 (;@1;)
          local.get $l1
          i32.const 48
          i32.add
          local.get $l1
          i32.const 160
          i32.add
          call $_ZN96_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hbed2967429de3e06E
          local.get $l1
          i64.load offset=48
          i32.wrap_i64
          br_if 2 (;@1;)
          local.get $l1
          i32.const 128
          i32.add
          local.get $l1
          i64.load offset=56
          call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
          local.get $l1
          i64.load offset=128
          i64.eqz
          i32.eqz
          br_if 2 (;@1;)
          local.get $l1
          i32.const 144
          i32.add
          i64.load
          local.set $l2
          local.get $l1
          i64.load offset=136
          local.set $l8
          i32.const 1048659
          i32.const 5
          call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
          local.set $l9
          local.get $l1
          local.get $l8
          local.get $l2
          call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h36445e94b15e4b89E
          i64.store offset=144
          local.get $l1
          local.get $p0
          i64.store offset=136
          local.get $l1
          local.get $l9
          i64.store offset=128
          local.get $l1
          i32.const 128
          i32.add
          i32.const 3
          call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E
          local.set $p0
          br 1 (;@2;)
        end
        local.get $l1
        i32.load offset=168
        local.get $l1
        i32.load offset=172
        call $_ZN107_$LT$soroban_sdk..vec..VecTryIter$LT$T$GT$$u20$as$u20$core..iter..traits..exact_size..ExactSizeIterator$GT$3len17h92b3c3ac3e773885E
        br_if 1 (;@1;)
        local.get $l1
        i32.const 80
        i32.add
        i32.const 1048664
        i32.const 4
        call $_ZN126_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$RF$str$GT$$GT$12try_from_val17h6167e90fc942376bE
        call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17hac49a8775e940f98E
        local.get $l1
        i64.load offset=88
        local.set $p0
      end
      local.get $l1
      i32.const 192
      i32.add
      global.set $__stack_pointer
      local.get $p0
      return
    end
    unreachable
    unreachable)
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h5bb243f4c9a8fdcaE (type $t0) (param $p0 i64) (param $p1 i64) (result i64)
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
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19vec_unpack_to_slice17h13b7b5195ebbe241E (type $t14) (param $p0 i64) (param $p1 i32)
    local.get $p0
    local.get $p1
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.const 8589934596
    call $_ZN17soroban_env_guest5guest3vec27vec_unpack_to_linear_memory17hbb96611dc359fde3E
    drop)
  (func $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE (type $t7) (param $p0 i32) (param $p1 i64)
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
  (func $addresse (type $t1) (param $p0 i64) (result i64)
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 77
      i64.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0)
  (func $bytes (type $t1) (param $p0 i64) (result i64)
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 72
      i64.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0)
  (func $bytes_n (type $t1) (param $p0 i64) (result i64)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i64.const 255
        i64.and
        i64.const 72
        i64.ne
        br_if 0 (;@2;)
        local.get $p0
        call $_ZN17soroban_env_guest5guest3buf9bytes_len17h783b00115bb1ca2bE
        i64.const -4294967296
        i64.and
        i64.const 38654705664
        i64.eq
        br_if 1 (;@1;)
      end
      unreachable
      unreachable
    end
    local.get $p0)
  (func $card (type $t1) (param $p0 i64) (result i64)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 0 (;@2;)
        local.get $p0
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        i32.const -14
        i32.add
        i32.const -4
        i32.gt_u
        br_if 1 (;@1;)
      end
      unreachable
      unreachable
    end
    local.get $p0
    i64.const -4294967296
    i64.and
    i64.const 4
    i64.or)
  (func $boolean (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32)
    block  ;; label = @1
      i32.const 1
      local.get $p0
      i32.wrap_i64
      i32.const 255
      i32.and
      local.tee $l1
      i32.const 0
      i32.ne
      i32.const 1
      i32.shl
      local.get $l1
      i32.const 1
      i32.eq
      select
      local.tee $l1
      i32.const 2
      i32.ne
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $l1
    i32.const 0
    i32.ne
    i64.extend_i32_u)
  (func $not (type $t1) (param $p0 i64) (result i64)
    block  ;; label = @1
      local.get $p0
      i64.const 254
      i64.and
      i64.eqz
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0
    i64.const -1
    i64.xor
    i64.const 1
    i64.and)
  (func $i128 (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    i32.const 8
    i32.add
    local.get $p0
    call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hd627965161c262deE
    block  ;; label = @1
      local.get $l1
      i64.load offset=8
      i64.eqz
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $l1
    i64.load offset=16
    local.get $l1
    i32.const 24
    i32.add
    i64.load
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h36445e94b15e4b89E
    local.set $p0
    local.get $l1
    i32.const 32
    i32.add
    global.set $__stack_pointer
    local.get $p0)
  (func $u128 (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i64)
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p0
          i32.wrap_i64
          i32.const 255
          i32.and
          local.tee $l1
          i32.const 68
          i32.eq
          br_if 0 (;@3;)
          block  ;; label = @4
            local.get $l1
            i32.const 10
            i32.ne
            br_if 0 (;@4;)
            local.get $p0
            i64.const 8
            i64.shr_u
            local.set $p0
            br 2 (;@2;)
          end
          unreachable
          unreachable
        end
        local.get $p0
        call $_ZN17soroban_env_guest5guest3int16obj_to_u128_hi6417hc25fd70bb9d05601E
        local.set $l2
        local.get $p0
        call $_ZN17soroban_env_guest5guest3int16obj_to_u128_lo6417he43d5142d6a48897E
        local.tee $p0
        i64.const 72057594037927935
        i64.gt_u
        local.get $l2
        i64.const 0
        i64.ne
        local.get $l2
        i64.eqz
        select
        br_if 1 (;@1;)
      end
      local.get $p0
      i64.const 8
      i64.shl
      i64.const 10
      i64.or
      return
    end
    local.get $l2
    local.get $p0
    call $_ZN17soroban_env_guest5guest3int20obj_from_u128_pieces17h4acfa69b076bf872E)
  (func $multi_args (type $t0) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32)
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 4
      i64.ne
      br_if 0 (;@1;)
      local.get $p1
      i32.wrap_i64
      i32.const 255
      i32.and
      local.tee $l2
      i32.const 2
      i32.ge_u
      br_if 0 (;@1;)
      local.get $p0
      i64.const -4294967292
      i64.and
      i64.const 4
      local.get $l2
      select
      return
    end
    unreachable
    unreachable)
  (func $map (type $t1) (param $p0 i64) (result i64)
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 76
      i64.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0)
  (func $vec (type $t1) (param $p0 i64) (result i64)
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 75
      i64.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0)
  (func $tuple (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i32) (local $l3 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i64.const 255
        i64.and
        i64.const 75
        i64.ne
        br_if 0 (;@2;)
        i32.const 0
        local.set $l2
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l2
            i32.const 16
            i32.eq
            br_if 1 (;@3;)
            local.get $l1
            i32.const 16
            i32.add
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
        local.get $p0
        local.get $l1
        i32.const 16
        i32.add
        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19vec_unpack_to_slice17h13b7b5195ebbe241E
        local.get $l1
        local.get $l1
        i64.load offset=16
        call $_ZN147_$LT$soroban_sdk..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h0ee459b69aad7985E
        local.get $l1
        i64.load
        i32.wrap_i64
        br_if 0 (;@2;)
        local.get $l1
        i64.load offset=24
        local.tee $p0
        i64.const 255
        i64.and
        i64.const 4
        i64.eq
        br_if 1 (;@1;)
      end
      unreachable
      unreachable
    end
    local.get $l1
    i64.load offset=8
    local.set $l3
    local.get $l1
    local.get $p0
    i64.const -4294967292
    i64.and
    i64.store offset=24
    local.get $l1
    local.get $l3
    i64.store offset=16
    local.get $l1
    i32.const 16
    i32.add
    i32.const 2
    call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E
    local.set $p0
    local.get $l1
    i32.const 32
    i32.add
    global.set $__stack_pointer
    local.get $p0)
  (func $option (type $t1) (param $p0 i64) (result i64)
    block  ;; label = @1
      local.get $p0
      i64.const 2
      i64.eq
      br_if 0 (;@1;)
      local.get $p0
      i64.const 255
      i64.and
      i64.const 4
      i64.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0
    i64.const -4294967296
    i64.and
    i64.const 4
    i64.or
    i64.const 2
    local.get $p0
    i64.const 2
    i64.ne
    select)
  (func $u256 (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32)
    block  ;; label = @1
      local.get $p0
      i32.wrap_i64
      i32.const 255
      i32.and
      local.tee $l1
      i32.const 12
      i32.eq
      br_if 0 (;@1;)
      local.get $l1
      i32.const 70
      i32.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0)
  (func $i256 (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32)
    block  ;; label = @1
      local.get $p0
      i32.wrap_i64
      i32.const 255
      i32.and
      local.tee $l1
      i32.const 13
      i32.eq
      br_if 0 (;@1;)
      local.get $l1
      i32.const 71
      i32.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0)
  (func $string (type $t1) (param $p0 i64) (result i64)
    block  ;; label = @1
      local.get $p0
      i64.const 255
      i64.and
      i64.const 73
      i64.eq
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $p0)
  (func $tuple_strukt (type $t1) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i32) (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32)
    global.get $__stack_pointer
    i32.const 64
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i64.const 255
        i64.and
        i64.const 75
        i64.ne
        br_if 0 (;@2;)
        i32.const 0
        local.set $l2
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l2
            i32.const 16
            i32.eq
            br_if 1 (;@3;)
            local.get $l1
            i32.const 48
            i32.add
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
        local.get $p0
        local.get $l1
        i32.const 48
        i32.add
        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19vec_unpack_to_slice17h13b7b5195ebbe241E
        local.get $l1
        local.get $l1
        i64.load offset=48
        call $_ZN161_$LT$soroban_other_custom_types_contract..Test$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17hfd3dae653f8c60a6E
        local.get $l1
        i32.load8_u offset=12
        local.tee $l3
        i32.const 2
        i32.eq
        br_if 0 (;@2;)
        local.get $l1
        i32.const 32
        i32.add
        i32.const 8
        i32.add
        local.tee $l4
        local.get $l1
        i32.const 8
        i32.add
        local.tee $l5
        i32.load
        i32.store
        local.get $l1
        i32.const 28
        i32.add
        i32.const 2
        i32.add
        local.get $l1
        i32.const 15
        i32.add
        local.tee $l6
        i32.load8_u
        i32.store8
        local.get $l1
        local.get $l1
        i64.load
        i64.store offset=32
        local.get $l1
        local.get $l1
        i32.load16_u offset=13 align=1
        i32.store16 offset=28
        local.get $l1
        i64.load offset=56
        call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h78558b51b19f7364E
        local.tee $l2
        i32.const 255
        i32.and
        i32.const 3
        i32.ne
        br_if 1 (;@1;)
      end
      unreachable
      unreachable
    end
    local.get $l5
    local.get $l4
    i32.load
    i32.store
    local.get $l6
    local.get $l1
    i32.const 28
    i32.add
    i32.const 2
    i32.add
    i32.load8_u
    i32.store8
    local.get $l1
    local.get $l1
    i64.load offset=32
    i64.store
    local.get $l1
    local.get $l1
    i32.load16_u offset=28
    i32.store16 offset=13 align=1
    local.get $l1
    local.get $l2
    i32.store8 offset=16
    local.get $l1
    local.get $l3
    i32.store8 offset=12
    local.get $l1
    call $_ZN35soroban_other_custom_types_contract171_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$soroban_other_custom_types_contract..Test$GT$$u20$for$u20$soroban_env_common..val..Val$GT$12try_from_val17hf4808d7c6a1e4682E
    local.set $p0
    local.get $l1
    local.get $l2
    call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h57035ce1931bf2f3E
    i64.store offset=56
    local.get $l1
    local.get $p0
    i64.store offset=48
    local.get $l1
    i32.const 48
    i32.add
    i32.const 2
    call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hd390c6a55d12eb33E
    local.set $p0
    local.get $l1
    i32.const 64
    i32.add
    global.set $__stack_pointer
    local.get $p0)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t13)
    unreachable
    unreachable)
  (func $_ (type $t13))
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048712))
  (global $__heap_base i32 (i32.const 1048720))
  (export "memory" (memory $memory))
  (export "hello" (func $hello))
  (export "auth" (func $auth))
  (export "get_count" (func $get_count))
  (export "inc" (func $inc))
  (export "woid" (func $woid))
  (export "val" (func $val))
  (export "u32_fail_on_even" (func $u32_fail_on_even))
  (export "u32_" (func $u32_))
  (export "i32_" (func $i32_))
  (export "i64_" (func $i64_))
  (export "strukt_hel" (func $strukt_hel))
  (export "strukt" (func $strukt))
  (export "simple" (func $simple))
  (export "complex" (func $complex))
  (export "addresse" (func $addresse))
  (export "bytes" (func $bytes))
  (export "bytes_n" (func $bytes_n))
  (export "card" (func $card))
  (export "boolean" (func $boolean))
  (export "not" (func $not))
  (export "i128" (func $i128))
  (export "u128" (func $u128))
  (export "multi_args" (func $multi_args))
  (export "map" (func $map))
  (export "vec" (func $vec))
  (export "tuple" (func $tuple))
  (export "option" (func $option))
  (export "u256" (func $u256))
  (export "i256" (func $i256))
  (export "string" (func $string))
  (export "tuple_strukt" (func $tuple_strukt))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (data $.rodata (i32.const 1048576) "abc\00\00\00\10\00\01\00\00\00\01\00\10\00\01\00\00\00\02\00\10\00\01\00\00\00FirstSecondThird\1c\00\10\00\05\00\00\00!\00\10\00\06\00\00\00'\00\10\00\05\00\00\00StructTupleEnumAssetVoidD\00\10\00\06\00\00\00J\00\10\00\05\00\00\00O\00\10\00\04\00\00\00S\00\10\00\05\00\00\00X\00\10\00\04\00\00\00auth"))
