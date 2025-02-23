(module $soroban_token_contract.wasm
  (type $t0 (func (param i64 i64 i64 i64) (result i64)))
  (type $t1 (func (param i64 i64) (result i64)))
  (type $t2 (func (param i64 i64 i64) (result i64)))
  (type $t3 (func (param i64) (result i64)))
  (type $t4 (func (result i64)))
  (type $t5 (func (param i32)))
  (type $t6 (func (param i32 i64 i32 i32)))
  (type $t7 (func (param i32) (result i64)))
  (type $t8 (func (param i64 i64) (result i32)))
  (type $t9 (func (param i64 i32 i32 i32 i32)))
  (type $t10 (func (param i32 i32) (result i64)))
  (type $t11 (func (param i32 i32 i32 i32) (result i64)))
  (type $t12 (func))
  (type $t13 (func (param i64)))
  (type $t14 (func (param i32 i64 i64)))
  (type $t15 (func (param i32 i64)))
  (type $t16 (func (result i32)))
  (type $t17 (func (param i64 i64 i64 i64 i32)))
  (type $t18 (func (param i64 i64 i64 i64)))
  (type $t19 (func (param i64 i64 i64)))
  (type $t20 (func (param i64 i64)))
  (type $t21 (func (param i32 i32)))
  (import "l" "7" (func $_ZN17soroban_env_guest5guest6ledger24extend_contract_data_ttl17hd4a5d6229e1b1295E (type $t0)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h7eec14f679e4a1f6E (type $t1)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17hbcc6972e2143ead5E (type $t2)))
  (import "a" "0" (func $_ZN17soroban_env_guest5guest7address12require_auth17h9cc50418802163a1E (type $t3)))
  (import "x" "1" (func $_ZN17soroban_env_guest5guest7context14contract_event17h428c4aad18d696f3E (type $t1)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h28127f747e256401E (type $t1)))
  (import "i" "8" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_hi6417hc8e99263eb8c864dE (type $t3)))
  (import "i" "7" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_lo6417h4f48d3d8445fdf5eE (type $t3)))
  (import "i" "6" (func $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17h4bb9fc4598b2d2deE (type $t1)))
  (import "b" "j" (func $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h798e74c72bae112eE (type $t1)))
  (import "m" "9" (func $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17h9e789c8bd223bb06E (type $t2)))
  (import "m" "a" (func $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17ha2ccd96abba396e2E (type $t0)))
  (import "x" "3" (func $_ZN17soroban_env_guest5guest7context19get_ledger_sequence17h68474e74ca530739E (type $t4)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17h905a7fcdca36de12E (type $t1)))
  (import "l" "8" (func $_ZN17soroban_env_guest5guest6ledger45extend_current_contract_instance_and_code_ttl17h7d3d3bc01b1a5c59E (type $t1)))
  (func $_ZN11soroban_sdk7storage10Persistent10extend_ttl17h7a4ae80dbca98ce1E (type $t5) (param $p0 i32)
    local.get $p0
    i64.const 1
    i32.const 501120
    i32.const 518400
    call $_ZN11soroban_sdk7storage7Storage10extend_ttl17h6c270e32f0544e17E)
  (func $_ZN11soroban_sdk7storage7Storage10extend_ttl17h6c270e32f0544e17E (type $t6) (param $p0 i32) (param $p1 i64) (param $p2 i32) (param $p3 i32)
    local.get $p0
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hdc69becf9bffd21fE
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
    call $_ZN17soroban_env_guest5guest6ledger24extend_contract_data_ttl17hd4a5d6229e1b1295E
    drop)
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hdc69becf9bffd21fE (type $t7) (param $p0 i32) (result i64)
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
            block  ;; label = @5
              local.get $p0
              i32.load
              br_table 3 (;@2;) 0 (;@5;) 1 (;@4;) 2 (;@3;) 3 (;@2;)
            end
            i32.const 1048653
            i32.const 7
            call $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17hb1d44846a518e0afE
            local.get $p0
            i64.load offset=8
            call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h985f9a93f1fc87f2E
            local.set $l2
            br 3 (;@1;)
          end
          i32.const 1048660
          i32.const 5
          call $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17hb1d44846a518e0afE
          local.get $p0
          i64.load offset=8
          call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h985f9a93f1fc87f2E
          local.set $l2
          br 2 (;@1;)
        end
        local.get $l1
        i32.const 1048665
        i32.const 5
        call $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17hb1d44846a518e0afE
        i64.store
        local.get $l1
        i32.const 1
        call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17h90422e63614012e8E
        local.set $l2
        br 1 (;@1;)
      end
      i32.const 1048644
      i32.const 9
      call $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17hb1d44846a518e0afE
      local.set $l2
      local.get $l1
      local.get $p0
      i64.load offset=16
      i64.store offset=8
      local.get $l1
      local.get $p0
      i64.load offset=8
      i64.store
      local.get $l2
      i32.const 1048588
      i32.const 2
      local.get $l1
      i32.const 2
      call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h2b73dbaf70d05f3fE
      call $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h985f9a93f1fc87f2E
      local.set $l2
    end
    local.get $l1
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l2)
  (func $_ZN11soroban_sdk7storage8Instance3get17hc23e2a19d3ae4762E (type $t5) (param $p0 i32)
    (local $l1 i32) (local $l2 i64) (local $l3 i32) (local $l4 i64) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    i64.const 0
    local.set $l2
    block  ;; label = @1
      block  ;; label = @2
        i64.const 27311646515383310
        i64.const 2
        call $_ZN11soroban_sdk7storage7Storage12has_internal17h39fdcf9e44930a82E
        i32.eqz
        br_if 0 (;@2;)
        i64.const 27311646515383310
        i64.const 2
        call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h7eec14f679e4a1f6E
        local.set $l2
        i32.const 0
        local.set $l3
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l3
            i32.const 24
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
        local.get $l2
        i64.const 255
        i64.and
        i64.const 76
        i64.ne
        br_if 1 (;@1;)
        local.get $l2
        i32.const 1048740
        i32.const 3
        local.get $l1
        i32.const 8
        i32.add
        i32.const 3
        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h0ecce68cab6f23ffE
        local.get $l1
        i64.load offset=8
        local.tee $l2
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 1 (;@1;)
        local.get $l1
        i64.load offset=16
        local.tee $l4
        i64.const 255
        i64.and
        i64.const 73
        i64.ne
        br_if 1 (;@1;)
        local.get $l1
        i64.load offset=24
        local.tee $l5
        i64.const 255
        i64.and
        i64.const 73
        i64.ne
        br_if 1 (;@1;)
        local.get $p0
        local.get $l2
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        i32.store offset=24
        local.get $p0
        local.get $l5
        i64.store offset=16
        local.get $p0
        local.get $l4
        i64.store offset=8
        i64.const 1
        local.set $l2
      end
      local.get $p0
      local.get $l2
      i64.store
      local.get $l1
      i32.const 32
      i32.add
      global.set $__stack_pointer
      return
    end
    unreachable
    unreachable)
  (func $_ZN11soroban_sdk7storage7Storage12has_internal17h39fdcf9e44930a82E (type $t8) (param $p0 i64) (param $p1 i64) (result i32)
    local.get $p0
    local.get $p1
    call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17h905a7fcdca36de12E
    i64.const 1
    i64.eq)
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h0ecce68cab6f23ffE (type $t9) (param $p0 i64) (param $p1 i32) (param $p2 i32) (param $p3 i32) (param $p4 i32)
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
    call $_ZN17soroban_env_guest5guest3map27map_unpack_to_linear_memory17ha2ccd96abba396e2E
    drop)
  (func $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17hb1d44846a518e0afE (type $t10) (param $p0 i32) (param $p1 i32) (result i64)
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
    call $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h798e74c72bae112eE)
  (func $_ZN74_$LT$U$u20$as$u20$soroban_env_common..convert..TryIntoVal$LT$E$C$T$GT$$GT$12try_into_val17h985f9a93f1fc87f2E (type $t1) (param $p0 i64) (param $p1 i64) (result i64)
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
    call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17h90422e63614012e8E
    local.set $p1
    local.get $l2
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $p1)
  (func $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17h90422e63614012e8E (type $t10) (param $p0 i32) (param $p1 i32) (result i64)
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
    call $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h28127f747e256401E)
  (func $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h2b73dbaf70d05f3fE (type $t11) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (result i64)
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
    call $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17h9e789c8bd223bb06E)
  (func $_ZN22soroban_token_contract5admin18read_administrator17ha8f705edf96e6020E (type $t4) (result i64)
    (local $l0 i32) (local $l1 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    i64.const 3
    i64.store offset=8
    block  ;; label = @1
      block  ;; label = @2
        local.get $l0
        i32.const 8
        i32.add
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hdc69becf9bffd21fE
        local.tee $l1
        i64.const 2
        call $_ZN11soroban_sdk7storage7Storage12has_internal17h39fdcf9e44930a82E
        i32.eqz
        br_if 0 (;@2;)
        local.get $l1
        i64.const 2
        call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h7eec14f679e4a1f6E
        local.tee $l1
        i64.const 255
        i64.and
        i64.const 77
        i64.eq
        br_if 1 (;@1;)
        unreachable
        unreachable
      end
      call $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E
      unreachable
    end
    local.get $l0
    i32.const 32
    i32.add
    global.set $__stack_pointer
    local.get $l1)
  (func $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E (type $t12)
    i32.const 1048670
    i32.const 43
    call $_ZN4core9panicking5panic17hcaca2598a27ec0fcE
    unreachable)
  (func $_ZN22soroban_token_contract5admin19write_administrator17h48a50a63fe0681bfE (type $t13) (param $p0 i64)
    (local $l1 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    i64.const 3
    i64.store offset=8
    local.get $l1
    i32.const 8
    i32.add
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hdc69becf9bffd21fE
    local.get $p0
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17hbcc6972e2143ead5E
    drop
    local.get $l1
    i32.const 32
    i32.add
    global.set $__stack_pointer)
  (func $_ZN22soroban_token_contract9allowance14read_allowance17h68f84a593cd97c74E (type $t14) (param $p0 i32) (param $p1 i64) (param $p2 i64)
    (local $l3 i32) (local $l4 i32) (local $l5 i64) (local $l6 i32)
    global.get $__stack_pointer
    i32.const 64
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $p2
    i64.store offset=16
    local.get $l3
    local.get $p1
    i64.store offset=8
    i64.const 0
    local.set $p2
    local.get $l3
    i64.const 0
    i64.store
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $l3
          call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hdc69becf9bffd21fE
          local.tee $p1
          i64.const 0
          call $_ZN11soroban_sdk7storage7Storage12has_internal17h39fdcf9e44930a82E
          br_if 0 (;@3;)
          i32.const 0
          local.set $l4
          i64.const 0
          local.set $p1
          br 1 (;@2;)
        end
        local.get $p1
        i64.const 0
        call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h7eec14f679e4a1f6E
        local.set $p2
        i32.const 0
        local.set $l4
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l4
            i32.const 16
            i32.eq
            br_if 1 (;@3;)
            local.get $l3
            i32.const 24
            i32.add
            local.get $l4
            i32.add
            i64.const 2
            i64.store
            local.get $l4
            i32.const 8
            i32.add
            local.set $l4
            br 0 (;@4;)
          end
        end
        local.get $p2
        i64.const 255
        i64.and
        i64.const 76
        i64.ne
        br_if 1 (;@1;)
        local.get $p2
        i32.const 1048628
        i32.const 2
        local.get $l3
        i32.const 24
        i32.add
        i32.const 2
        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_unpack_to_slice17h0ecce68cab6f23ffE
        local.get $l3
        i32.const 40
        i32.add
        local.get $l3
        i64.load offset=24
        call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h62f965de1af697a0E
        local.get $l3
        i64.load offset=40
        i64.eqz
        i32.eqz
        br_if 1 (;@1;)
        local.get $l3
        i64.load offset=32
        local.tee $p2
        i64.const 255
        i64.and
        i64.const 4
        i64.ne
        br_if 1 (;@1;)
        local.get $l3
        i64.load offset=48
        local.set $l5
        i64.const 0
        local.get $l3
        i32.const 56
        i32.add
        i64.load
        call $_ZN11soroban_sdk6ledger6Ledger8sequence17hd691eb2f1e4efbffE
        local.get $p2
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        local.tee $l4
        i32.gt_u
        local.tee $l6
        select
        local.set $p1
        i64.const 0
        local.get $l5
        local.get $l6
        select
        local.set $p2
      end
      local.get $p0
      local.get $p1
      i64.store offset=8
      local.get $p0
      local.get $p2
      i64.store
      local.get $p0
      local.get $l4
      i32.store offset=16
      local.get $l3
      i32.const 64
      i32.add
      global.set $__stack_pointer
      return
    end
    unreachable
    unreachable)
  (func $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h62f965de1af697a0E (type $t15) (param $p0 i32) (param $p1 i64)
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
        call $_ZN17soroban_env_guest5guest3int16obj_to_i128_hi6417hc8e99263eb8c864dE
        local.set $l3
        local.get $p1
        call $_ZN17soroban_env_guest5guest3int16obj_to_i128_lo6417h4f48d3d8445fdf5eE
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
  (func $_ZN11soroban_sdk6ledger6Ledger8sequence17hd691eb2f1e4efbffE (type $t16) (result i32)
    call $_ZN17soroban_env_guest5guest7context19get_ledger_sequence17h68474e74ca530739E
    i64.const 32
    i64.shr_u
    i32.wrap_i64)
  (func $_ZN22soroban_token_contract9allowance15write_allowance17h4229c36eb0b4fbe4E (type $t17) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i32)
    (local $l5 i32) (local $l6 i32)
    global.get $__stack_pointer
    i32.const 80
    i32.sub
    local.tee $l5
    global.set $__stack_pointer
    block  ;; label = @1
      local.get $p2
      i64.const 0
      i64.ne
      local.get $p3
      i64.const 0
      i64.gt_s
      local.get $p3
      i64.eqz
      select
      local.tee $l6
      i32.eqz
      br_if 0 (;@1;)
      call $_ZN11soroban_sdk6ledger6Ledger8sequence17hd691eb2f1e4efbffE
      local.get $p4
      i32.le_u
      br_if 0 (;@1;)
      call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
      unreachable
    end
    local.get $l5
    local.get $p1
    i64.store offset=32
    local.get $l5
    local.get $p0
    i64.store offset=24
    local.get $l5
    i64.const 0
    i64.store offset=16
    local.get $l5
    local.get $p1
    i64.store offset=56
    local.get $l5
    local.get $p0
    i64.store offset=48
    local.get $l5
    i64.const 0
    i64.store offset=40
    local.get $l5
    i32.const 40
    i32.add
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hdc69becf9bffd21fE
    local.set $p1
    local.get $l5
    local.get $p2
    local.get $p3
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h7f8f9500d964abdeE
    local.get $l5
    local.get $p4
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.store offset=72
    local.get $l5
    local.get $l5
    i64.load offset=8
    i64.store offset=64
    local.get $p1
    i32.const 1048628
    i32.const 2
    local.get $l5
    i32.const 64
    i32.add
    i32.const 2
    call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h2b73dbaf70d05f3fE
    i64.const 0
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17hbcc6972e2143ead5E
    drop
    block  ;; label = @1
      local.get $l6
      i32.eqz
      br_if 0 (;@1;)
      block  ;; label = @2
        local.get $p4
        call $_ZN11soroban_sdk6ledger6Ledger8sequence17hd691eb2f1e4efbffE
        local.tee $l6
        i32.ge_u
        br_if 0 (;@2;)
        call $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E
        unreachable
      end
      local.get $l5
      i32.const 16
      i32.add
      i64.const 0
      local.get $p4
      local.get $l6
      i32.sub
      local.tee $p4
      local.get $p4
      call $_ZN11soroban_sdk7storage7Storage10extend_ttl17h6c270e32f0544e17E
    end
    local.get $l5
    i32.const 80
    i32.add
    global.set $__stack_pointer)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t12)
    unreachable
    unreachable)
  (func $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h7f8f9500d964abdeE (type $t14) (param $p0 i32) (param $p1 i64) (param $p2 i64)
    block  ;; label = @1
      block  ;; label = @2
        local.get $p1
        i64.const 36028797018963968
        i64.add
        i64.const 72057594037927935
        i64.gt_u
        br_if 0 (;@2;)
        local.get $p1
        local.get $p1
        i64.xor
        local.get $p1
        i64.const 63
        i64.shr_s
        local.get $p2
        i64.xor
        i64.or
        i64.const 0
        i64.ne
        br_if 0 (;@2;)
        local.get $p1
        i64.const 8
        i64.shl
        i64.const 11
        i64.or
        local.set $p1
        br 1 (;@1;)
      end
      local.get $p2
      local.get $p1
      call $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17h4bb9fc4598b2d2deE
      local.set $p1
    end
    local.get $p0
    local.get $p1
    i64.store offset=8
    local.get $p0
    i64.const 0
    i64.store)
  (func $_ZN22soroban_token_contract9allowance15spend_allowance17h2b3a85728e7d920bE (type $t18) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64)
    (local $l4 i32) (local $l5 i64) (local $l6 i32) (local $l7 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l4
    global.set $__stack_pointer
    local.get $l4
    i32.const 8
    i32.add
    local.get $p0
    local.get $p1
    call $_ZN22soroban_token_contract9allowance14read_allowance17h68f84a593cd97c74E
    block  ;; label = @1
      local.get $l4
      i64.load offset=8
      local.tee $l5
      local.get $p2
      i64.lt_u
      local.tee $l6
      local.get $l4
      i32.const 16
      i32.add
      i64.load
      local.tee $l7
      local.get $p3
      i64.lt_s
      local.get $l7
      local.get $p3
      i64.eq
      select
      br_if 0 (;@1;)
      block  ;; label = @2
        local.get $p2
        i64.const 0
        i64.ne
        local.get $p3
        i64.const 0
        i64.gt_s
        local.get $p3
        i64.eqz
        select
        i32.eqz
        br_if 0 (;@2;)
        local.get $p0
        local.get $p1
        local.get $l5
        local.get $p2
        i64.sub
        local.get $l7
        local.get $p3
        i64.sub
        local.get $l6
        i64.extend_i32_u
        i64.sub
        local.get $l4
        i32.load offset=24
        call $_ZN22soroban_token_contract9allowance15write_allowance17h4229c36eb0b4fbe4E
      end
      local.get $l4
      i32.const 32
      i32.add
      global.set $__stack_pointer
      return
    end
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN22soroban_token_contract7balance12read_balance17h2e99a4d04dcb320bE (type $t15) (param $p0 i32) (param $p1 i64)
    (local $l2 i32) (local $l3 i64) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    i64.const 1
    i64.store
    local.get $l2
    local.get $p1
    i64.store offset=8
    i64.const 0
    local.set $p1
    i64.const 0
    local.set $l3
    block  ;; label = @1
      block  ;; label = @2
        local.get $l2
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hdc69becf9bffd21fE
        local.tee $l4
        i64.const 1
        call $_ZN11soroban_sdk7storage7Storage12has_internal17h39fdcf9e44930a82E
        i32.eqz
        br_if 0 (;@2;)
        local.get $l2
        i32.const 24
        i32.add
        local.get $l4
        i64.const 1
        call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h7eec14f679e4a1f6E
        call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h62f965de1af697a0E
        local.get $l2
        i64.load offset=24
        i64.eqz
        i32.eqz
        br_if 1 (;@1;)
        local.get $l2
        i32.const 40
        i32.add
        i64.load
        local.set $l3
        local.get $l2
        i64.load offset=32
        local.set $p1
        local.get $l2
        call $_ZN11soroban_sdk7storage10Persistent10extend_ttl17h7a4ae80dbca98ce1E
      end
      local.get $p0
      local.get $l3
      i64.store offset=8
      local.get $p0
      local.get $p1
      i64.store
      local.get $l2
      i32.const 48
      i32.add
      global.set $__stack_pointer
      return
    end
    unreachable
    unreachable)
  (func $_ZN22soroban_token_contract7balance13write_balance17hbec9b517a1a30924E (type $t19) (param $p0 i64) (param $p1 i64) (param $p2 i64)
    (local $l3 i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    i64.const 1
    i64.store offset=24
    local.get $l3
    local.get $p0
    i64.store offset=32
    local.get $l3
    i32.const 24
    i32.add
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hdc69becf9bffd21fE
    local.set $p0
    local.get $l3
    i32.const 8
    i32.add
    local.get $p1
    local.get $p2
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h7f8f9500d964abdeE
    local.get $p0
    local.get $l3
    i64.load offset=16
    i64.const 1
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17hbcc6972e2143ead5E
    drop
    local.get $l3
    i32.const 24
    i32.add
    call $_ZN11soroban_sdk7storage10Persistent10extend_ttl17h7a4ae80dbca98ce1E
    local.get $l3
    i32.const 48
    i32.add
    global.set $__stack_pointer)
  (func $_ZN22soroban_token_contract7balance15receive_balance17h4e7c7c05d90eebafE (type $t19) (param $p0 i64) (param $p1 i64) (param $p2 i64)
    (local $l3 i32) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $p0
    call $_ZN22soroban_token_contract7balance12read_balance17h2e99a4d04dcb320bE
    block  ;; label = @1
      local.get $l3
      i32.const 8
      i32.add
      i64.load
      local.tee $l4
      local.get $p2
      i64.xor
      i64.const -1
      i64.xor
      local.get $l4
      local.get $l4
      local.get $p2
      i64.add
      local.get $l3
      i64.load
      local.tee $p2
      local.get $p1
      i64.add
      local.tee $p1
      local.get $p2
      i64.lt_u
      i64.extend_i32_u
      i64.add
      local.tee $p2
      i64.xor
      i64.and
      i64.const 0
      i64.lt_s
      br_if 0 (;@1;)
      local.get $p0
      local.get $p1
      local.get $p2
      call $_ZN22soroban_token_contract7balance13write_balance17hbec9b517a1a30924E
      local.get $l3
      i32.const 16
      i32.add
      global.set $__stack_pointer
      return
    end
    call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
    unreachable)
  (func $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E (type $t12)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN22soroban_token_contract7balance13spend_balance17h77201ba14246e2c1E (type $t19) (param $p0 i64) (param $p1 i64) (param $p2 i64)
    (local $l3 i32) (local $l4 i64) (local $l5 i32) (local $l6 i64)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $p0
    call $_ZN22soroban_token_contract7balance12read_balance17h2e99a4d04dcb320bE
    block  ;; label = @1
      block  ;; label = @2
        local.get $l3
        i64.load
        local.tee $l4
        local.get $p1
        i64.lt_u
        local.tee $l5
        local.get $l3
        i32.const 8
        i32.add
        i64.load
        local.tee $l6
        local.get $p2
        i64.lt_s
        local.get $l6
        local.get $p2
        i64.eq
        select
        br_if 0 (;@2;)
        local.get $l6
        local.get $p2
        i64.xor
        local.get $l6
        local.get $l6
        local.get $p2
        i64.sub
        local.get $l5
        i64.extend_i32_u
        i64.sub
        local.tee $p2
        i64.xor
        i64.and
        i64.const 0
        i64.ge_s
        br_if 1 (;@1;)
        call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
        unreachable
      end
      call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
      unreachable
    end
    local.get $p0
    local.get $l4
    local.get $p1
    i64.sub
    local.get $p2
    call $_ZN22soroban_token_contract7balance13write_balance17hbec9b517a1a30924E
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN22soroban_token_contract8contract24check_nonnegative_amount17h5fe1699cfd7d856bE (type $t20) (param $p0 i64) (param $p1 i64)
    block  ;; label = @1
      local.get $p1
      i64.const 0
      i64.lt_s
      br_if 0 (;@1;)
      return
    end
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $initialize (type $t0) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (result i64)
    (local $l4 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l4
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
        i64.const 4
        i64.ne
        br_if 0 (;@2;)
        local.get $p2
        i64.const 255
        i64.and
        i64.const 73
        i64.ne
        br_if 0 (;@2;)
        local.get $p3
        i64.const 255
        i64.and
        i64.const 73
        i64.ne
        br_if 0 (;@2;)
        local.get $l4
        i64.const 3
        i64.store offset=8
        local.get $l4
        i32.const 8
        i32.add
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hdc69becf9bffd21fE
        i64.const 2
        call $_ZN11soroban_sdk7storage7Storage12has_internal17h39fdcf9e44930a82E
        br_if 1 (;@1;)
        local.get $p0
        call $_ZN22soroban_token_contract5admin19write_administrator17h48a50a63fe0681bfE
        local.get $p1
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        i32.const 18
        i32.gt_u
        br_if 1 (;@1;)
        local.get $l4
        local.get $p3
        i64.store offset=24
        local.get $l4
        local.get $p2
        i64.store offset=16
        local.get $l4
        local.get $p1
        i64.const -4294967292
        i64.and
        i64.store offset=8
        i64.const 27311646515383310
        i32.const 1048740
        i32.const 3
        local.get $l4
        i32.const 8
        i32.add
        i32.const 3
        call $_ZN74_$LT$soroban_sdk..env..Env$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h2b73dbaf70d05f3fE
        i64.const 2
        call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17hbcc6972e2143ead5E
        drop
        local.get $l4
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
  (func $mint (type $t1) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32) (local $l3 i64) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 48
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
      i32.const 24
      i32.add
      local.get $p1
      call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h62f965de1af697a0E
      local.get $l2
      i64.load offset=24
      i64.eqz
      i32.eqz
      br_if 0 (;@1;)
      local.get $l2
      i64.load offset=32
      local.tee $p1
      local.get $l2
      i32.const 40
      i32.add
      i64.load
      local.tee $l3
      call $_ZN22soroban_token_contract8contract24check_nonnegative_amount17h5fe1699cfd7d856bE
      call $_ZN22soroban_token_contract5admin18read_administrator17ha8f705edf96e6020E
      local.tee $l4
      call $_ZN17soroban_env_guest5guest7address12require_auth17h9cc50418802163a1E
      drop
      call $_ZN11soroban_sdk7storage8Instance10extend_ttl17h17f58be25d2ad2f9E
      local.get $p0
      local.get $p1
      local.get $l3
      call $_ZN22soroban_token_contract7balance15receive_balance17h4e7c7c05d90eebafE
      local.get $l2
      local.get $p0
      i64.store offset=40
      local.get $l2
      local.get $l4
      i64.store offset=32
      local.get $l2
      i64.const 3404527886
      i64.store offset=24
      local.get $l2
      i32.const 24
      i32.add
      call $_ZN11soroban_sdk5tuple179_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$LP$T0$C$T1$C$T2$RP$$GT$$u20$for$u20$soroban_sdk..vec..Vec$LT$soroban_env_common..val..Val$GT$$GT$12try_from_val17h49d70eb3e60adb07E
      local.set $p0
      local.get $l2
      i32.const 8
      i32.add
      local.get $p1
      local.get $l3
      call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h7f8f9500d964abdeE
      local.get $p0
      local.get $l2
      i64.load offset=16
      call $_ZN17soroban_env_guest5guest7context14contract_event17h428c4aad18d696f3E
      drop
      local.get $l2
      i32.const 48
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    unreachable
    unreachable)
  (func $_ZN11soroban_sdk7storage8Instance10extend_ttl17h17f58be25d2ad2f9E (type $t12)
    i64.const 445302209249284
    i64.const 519519244124164
    call $_ZN17soroban_env_guest5guest6ledger45extend_current_contract_instance_and_code_ttl17h7d3d3bc01b1a5c59E
    drop)
  (func $_ZN11soroban_sdk5tuple179_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$LP$T0$C$T1$C$T2$RP$$GT$$u20$for$u20$soroban_sdk..vec..Vec$LT$soroban_env_common..val..Val$GT$$GT$12try_from_val17h49d70eb3e60adb07E (type $t7) (param $p0 i32) (result i64)
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
        call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17h90422e63614012e8E
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
  (func $set_admin (type $t3) (param $p0 i64) (result i64)
    (local $l1 i64)
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
    call $_ZN22soroban_token_contract5admin18read_administrator17ha8f705edf96e6020E
    local.tee $l1
    call $_ZN17soroban_env_guest5guest7address12require_auth17h9cc50418802163a1E
    drop
    call $_ZN11soroban_sdk7storage8Instance10extend_ttl17h17f58be25d2ad2f9E
    local.get $p0
    call $_ZN22soroban_token_contract5admin19write_administrator17h48a50a63fe0681bfE
    i64.const 4083516257707209486
    local.get $l1
    call $_ZN11soroban_sdk5tuple174_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$LP$T0$C$T1$RP$$GT$$u20$for$u20$soroban_sdk..vec..Vec$LT$soroban_env_common..val..Val$GT$$GT$12try_from_val17hc6db7778c471c5e7E
    local.get $p0
    call $_ZN17soroban_env_guest5guest7context14contract_event17h428c4aad18d696f3E
    drop
    i64.const 2)
  (func $_ZN11soroban_sdk5tuple174_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$LP$T0$C$T1$RP$$GT$$u20$for$u20$soroban_sdk..vec..Vec$LT$soroban_env_common..val..Val$GT$$GT$12try_from_val17hc6db7778c471c5e7E (type $t1) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32) (local $l3 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    local.get $p1
    i64.store offset=8
    local.get $l2
    local.get $p0
    i64.store
    i32.const 0
    local.set $l3
    loop (result i64)  ;; label = @1
      block  ;; label = @2
        local.get $l3
        i32.const 16
        i32.ne
        br_if 0 (;@2;)
        i32.const 0
        local.set $l3
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l3
            i32.const 16
            i32.eq
            br_if 1 (;@3;)
            local.get $l2
            i32.const 16
            i32.add
            local.get $l3
            i32.add
            local.get $l2
            local.get $l3
            i32.add
            i64.load
            i64.store
            local.get $l3
            i32.const 8
            i32.add
            local.set $l3
            br 0 (;@4;)
          end
        end
        local.get $l2
        i32.const 16
        i32.add
        i32.const 2
        call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17h90422e63614012e8E
        local.set $p1
        local.get $l2
        i32.const 32
        i32.add
        global.set $__stack_pointer
        local.get $p1
        return
      end
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
      br 0 (;@1;)
    end)
  (func $allowance (type $t1) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32)
    global.get $__stack_pointer
    i32.const 48
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
      local.get $p1
      i64.const 255
      i64.and
      i64.const 77
      i64.ne
      br_if 0 (;@1;)
      call $_ZN11soroban_sdk7storage8Instance10extend_ttl17h17f58be25d2ad2f9E
      local.get $l2
      i32.const 24
      i32.add
      local.get $p0
      local.get $p1
      call $_ZN22soroban_token_contract9allowance14read_allowance17h68f84a593cd97c74E
      local.get $l2
      i32.const 8
      i32.add
      local.get $l2
      i64.load offset=24
      local.get $l2
      i32.const 32
      i32.add
      i64.load
      call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h7f8f9500d964abdeE
      local.get $l2
      i64.load offset=16
      local.set $p0
      local.get $l2
      i32.const 48
      i32.add
      global.set $__stack_pointer
      local.get $p0
      return
    end
    unreachable
    unreachable)
  (func $approve (type $t0) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (result i64)
    (local $l4 i32) (local $l5 i64) (local $l6 i64)
    global.get $__stack_pointer
    i32.const 64
    i32.sub
    local.tee $l4
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
      local.get $l4
      i32.const 24
      i32.add
      local.get $p2
      call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h62f965de1af697a0E
      local.get $l4
      i64.load offset=24
      i64.eqz
      i32.eqz
      br_if 0 (;@1;)
      local.get $p3
      i64.const 255
      i64.and
      i64.const 4
      i64.ne
      br_if 0 (;@1;)
      local.get $l4
      i32.const 40
      i32.add
      i64.load
      local.set $p2
      local.get $l4
      i64.load offset=32
      local.set $l5
      local.get $p0
      call $_ZN17soroban_env_guest5guest7address12require_auth17h9cc50418802163a1E
      drop
      local.get $l5
      local.get $p2
      call $_ZN22soroban_token_contract8contract24check_nonnegative_amount17h5fe1699cfd7d856bE
      call $_ZN11soroban_sdk7storage8Instance10extend_ttl17h17f58be25d2ad2f9E
      local.get $p0
      local.get $p1
      local.get $l5
      local.get $p2
      local.get $p3
      i64.const 32
      i64.shr_u
      i32.wrap_i64
      call $_ZN22soroban_token_contract9allowance15write_allowance17h4229c36eb0b4fbe4E
      i32.const 1048713
      i32.const 7
      call $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17hb1d44846a518e0afE
      local.set $l6
      local.get $l4
      local.get $p1
      i64.store offset=40
      local.get $l4
      local.get $p0
      i64.store offset=32
      local.get $l4
      local.get $l6
      i64.store offset=24
      local.get $l4
      i32.const 24
      i32.add
      call $_ZN11soroban_sdk5tuple179_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$LP$T0$C$T1$C$T2$RP$$GT$$u20$for$u20$soroban_sdk..vec..Vec$LT$soroban_env_common..val..Val$GT$$GT$12try_from_val17h49d70eb3e60adb07E
      local.set $p0
      local.get $l4
      i32.const 8
      i32.add
      local.get $l5
      local.get $p2
      call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h7f8f9500d964abdeE
      local.get $l4
      local.get $p3
      i64.const -4294967292
      i64.and
      i64.store offset=56
      local.get $l4
      local.get $l4
      i64.load offset=16
      i64.store offset=48
      local.get $p0
      local.get $l4
      i32.const 48
      i32.add
      i32.const 2
      call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17h90422e63614012e8E
      call $_ZN17soroban_env_guest5guest7context14contract_event17h428c4aad18d696f3E
      drop
      local.get $l4
      i32.const 64
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    unreachable
    unreachable)
  (func $balance (type $t3) (param $p0 i64) (result i64)
    (local $l1 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
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
    call $_ZN11soroban_sdk7storage8Instance10extend_ttl17h17f58be25d2ad2f9E
    local.get $l1
    i32.const 16
    i32.add
    local.get $p0
    call $_ZN22soroban_token_contract7balance12read_balance17h2e99a4d04dcb320bE
    local.get $l1
    local.get $l1
    i64.load offset=16
    local.get $l1
    i32.const 24
    i32.add
    i64.load
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h7f8f9500d964abdeE
    local.get $l1
    i64.load offset=8
    local.set $p0
    local.get $l1
    i32.const 32
    i32.add
    global.set $__stack_pointer
    local.get $p0)
  (func $transfer (type $t2) (param $p0 i64) (param $p1 i64) (param $p2 i64) (result i64)
    (local $l3 i32) (local $l4 i64)
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
      i32.const 8
      i32.add
      local.get $p2
      call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h62f965de1af697a0E
      local.get $l3
      i64.load offset=8
      i64.eqz
      i32.eqz
      br_if 0 (;@1;)
      local.get $l3
      i32.const 24
      i32.add
      i64.load
      local.set $p2
      local.get $l3
      i64.load offset=16
      local.set $l4
      local.get $p0
      call $_ZN17soroban_env_guest5guest7address12require_auth17h9cc50418802163a1E
      drop
      local.get $l4
      local.get $p2
      call $_ZN22soroban_token_contract8contract24check_nonnegative_amount17h5fe1699cfd7d856bE
      call $_ZN11soroban_sdk7storage8Instance10extend_ttl17h17f58be25d2ad2f9E
      local.get $p0
      local.get $l4
      local.get $p2
      call $_ZN22soroban_token_contract7balance13spend_balance17h77201ba14246e2c1E
      local.get $p1
      local.get $l4
      local.get $p2
      call $_ZN22soroban_token_contract7balance15receive_balance17h4e7c7c05d90eebafE
      local.get $p0
      local.get $p1
      local.get $l4
      local.get $p2
      call $_ZN17soroban_token_sdk5event6Events8transfer17h2970221061257c84E
      local.get $l3
      i32.const 32
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    unreachable
    unreachable)
  (func $_ZN17soroban_token_sdk5event6Events8transfer17h2970221061257c84E (type $t18) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64)
    (local $l4 i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l4
    global.set $__stack_pointer
    local.get $l4
    local.get $p1
    i64.store offset=40
    local.get $l4
    local.get $p0
    i64.store offset=32
    local.get $l4
    i64.const 65154533130155790
    i64.store offset=24
    local.get $l4
    i32.const 24
    i32.add
    call $_ZN11soroban_sdk5tuple179_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$LP$T0$C$T1$C$T2$RP$$GT$$u20$for$u20$soroban_sdk..vec..Vec$LT$soroban_env_common..val..Val$GT$$GT$12try_from_val17h49d70eb3e60adb07E
    local.set $p1
    local.get $l4
    i32.const 8
    i32.add
    local.get $p2
    local.get $p3
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h7f8f9500d964abdeE
    local.get $p1
    local.get $l4
    i64.load offset=16
    call $_ZN17soroban_env_guest5guest7context14contract_event17h428c4aad18d696f3E
    drop
    local.get $l4
    i32.const 48
    i32.add
    global.set $__stack_pointer)
  (func $transfer_from (type $t0) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (result i64)
    (local $l4 i32) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l4
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
      local.get $p2
      i64.const 255
      i64.and
      i64.const 77
      i64.ne
      br_if 0 (;@1;)
      local.get $l4
      i32.const 8
      i32.add
      local.get $p3
      call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h62f965de1af697a0E
      local.get $l4
      i64.load offset=8
      i64.eqz
      i32.eqz
      br_if 0 (;@1;)
      local.get $l4
      i32.const 24
      i32.add
      i64.load
      local.set $p3
      local.get $l4
      i64.load offset=16
      local.set $l5
      local.get $p0
      call $_ZN17soroban_env_guest5guest7address12require_auth17h9cc50418802163a1E
      drop
      local.get $l5
      local.get $p3
      call $_ZN22soroban_token_contract8contract24check_nonnegative_amount17h5fe1699cfd7d856bE
      call $_ZN11soroban_sdk7storage8Instance10extend_ttl17h17f58be25d2ad2f9E
      local.get $p1
      local.get $p0
      local.get $l5
      local.get $p3
      call $_ZN22soroban_token_contract9allowance15spend_allowance17h2b3a85728e7d920bE
      local.get $p1
      local.get $l5
      local.get $p3
      call $_ZN22soroban_token_contract7balance13spend_balance17h77201ba14246e2c1E
      local.get $p2
      local.get $l5
      local.get $p3
      call $_ZN22soroban_token_contract7balance15receive_balance17h4e7c7c05d90eebafE
      local.get $p1
      local.get $p2
      local.get $l5
      local.get $p3
      call $_ZN17soroban_token_sdk5event6Events8transfer17h2970221061257c84E
      local.get $l4
      i32.const 32
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    unreachable
    unreachable)
  (func $burn (type $t1) (param $p0 i64) (param $p1 i64) (result i64)
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
      call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h62f965de1af697a0E
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
      local.get $p0
      call $_ZN17soroban_env_guest5guest7address12require_auth17h9cc50418802163a1E
      drop
      local.get $l3
      local.get $p1
      call $_ZN22soroban_token_contract8contract24check_nonnegative_amount17h5fe1699cfd7d856bE
      call $_ZN11soroban_sdk7storage8Instance10extend_ttl17h17f58be25d2ad2f9E
      local.get $p0
      local.get $l3
      local.get $p1
      call $_ZN22soroban_token_contract7balance13spend_balance17h77201ba14246e2c1E
      local.get $p0
      local.get $l3
      local.get $p1
      call $_ZN17soroban_token_sdk5event6Events4burn17h4192e2cb04627615E
      local.get $l2
      i32.const 32
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    unreachable
    unreachable)
  (func $_ZN17soroban_token_sdk5event6Events4burn17h4192e2cb04627615E (type $t19) (param $p0 i64) (param $p1 i64) (param $p2 i64)
    (local $l3 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    i64.const 2678977294
    local.get $p0
    call $_ZN11soroban_sdk5tuple174_$LT$impl$u20$soroban_env_common..convert..TryFromVal$LT$soroban_sdk..env..Env$C$$LP$T0$C$T1$RP$$GT$$u20$for$u20$soroban_sdk..vec..Vec$LT$soroban_env_common..val..Val$GT$$GT$12try_from_val17hc6db7778c471c5e7E
    local.set $p0
    local.get $l3
    local.get $p1
    local.get $p2
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17h7f8f9500d964abdeE
    local.get $p0
    local.get $l3
    i64.load offset=8
    call $_ZN17soroban_env_guest5guest7context14contract_event17h428c4aad18d696f3E
    drop
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $burn_from (type $t2) (param $p0 i64) (param $p1 i64) (param $p2 i64) (result i64)
    (local $l3 i32) (local $l4 i64)
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
      i32.const 8
      i32.add
      local.get $p2
      call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h62f965de1af697a0E
      local.get $l3
      i64.load offset=8
      i64.eqz
      i32.eqz
      br_if 0 (;@1;)
      local.get $l3
      i32.const 24
      i32.add
      i64.load
      local.set $p2
      local.get $l3
      i64.load offset=16
      local.set $l4
      local.get $p0
      call $_ZN17soroban_env_guest5guest7address12require_auth17h9cc50418802163a1E
      drop
      local.get $l4
      local.get $p2
      call $_ZN22soroban_token_contract8contract24check_nonnegative_amount17h5fe1699cfd7d856bE
      call $_ZN11soroban_sdk7storage8Instance10extend_ttl17h17f58be25d2ad2f9E
      local.get $p1
      local.get $p0
      local.get $l4
      local.get $p2
      call $_ZN22soroban_token_contract9allowance15spend_allowance17h2b3a85728e7d920bE
      local.get $p1
      local.get $l4
      local.get $p2
      call $_ZN22soroban_token_contract7balance13spend_balance17h77201ba14246e2c1E
      local.get $p1
      local.get $l4
      local.get $p2
      call $_ZN17soroban_token_sdk5event6Events4burn17h4192e2cb04627615E
      local.get $l3
      i32.const 32
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    unreachable
    unreachable)
  (func $decimals (type $t4) (result i64)
    (local $l0 i32) (local $l1 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    call $_ZN11soroban_sdk7storage8Instance3get17hc23e2a19d3ae4762E
    block  ;; label = @1
      local.get $l0
      i64.load
      i64.const 0
      i64.ne
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $l0
    i64.load32_u offset=24
    local.set $l1
    local.get $l0
    i32.const 32
    i32.add
    global.set $__stack_pointer
    local.get $l1
    i64.const 32
    i64.shl
    i64.const 4
    i64.or)
  (func $name (type $t4) (result i64)
    (local $l0 i32) (local $l1 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    call $_ZN11soroban_sdk7storage8Instance3get17hc23e2a19d3ae4762E
    block  ;; label = @1
      local.get $l0
      i64.load
      i64.const 0
      i64.ne
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $l0
    i64.load offset=8
    local.set $l1
    local.get $l0
    i32.const 32
    i32.add
    global.set $__stack_pointer
    local.get $l1)
  (func $symbol (type $t4) (result i64)
    (local $l0 i32) (local $l1 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    call $_ZN11soroban_sdk7storage8Instance3get17hc23e2a19d3ae4762E
    block  ;; label = @1
      local.get $l0
      i64.load
      i64.const 0
      i64.ne
      br_if 0 (;@1;)
      unreachable
      unreachable
    end
    local.get $l0
    i64.load offset=16
    local.set $l1
    local.get $l0
    i32.const 32
    i32.add
    global.set $__stack_pointer
    local.get $l1)
  (func $_ZN4core9panicking5panic17hcaca2598a27ec0fcE (type $t21) (param $p0 i32) (param $p1 i32)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ (type $t12))
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048764))
  (global $__heap_base i32 (i32.const 1048768))
  (export "memory" (memory $memory))
  (export "initialize" (func $initialize))
  (export "mint" (func $mint))
  (export "set_admin" (func $set_admin))
  (export "allowance" (func $allowance))
  (export "approve" (func $approve))
  (export "balance" (func $balance))
  (export "transfer" (func $transfer))
  (export "transfer_from" (func $transfer_from))
  (export "burn" (func $burn))
  (export "burn_from" (func $burn_from))
  (export "decimals" (func $decimals))
  (export "name" (func $name))
  (export "symbol" (func $symbol))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (data $.rodata (i32.const 1048576) "fromspender\00\00\00\10\00\04\00\00\00\04\00\10\00\07\00\00\00amountexpiration_ledger\00\1c\00\10\00\06\00\00\00\22\00\10\00\11\00\00\00AllowanceBalanceStateAdmincalled `Option::unwrap()` on a `None` valueapprovedecimalnamesymbol\00\00\00\90\00\10\00\07\00\00\00\97\00\10\00\04\00\00\00\9b\00\10\00\06\00\00\00"))
