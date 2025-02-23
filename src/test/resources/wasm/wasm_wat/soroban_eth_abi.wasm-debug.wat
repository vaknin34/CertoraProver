(module $soroban_eth_abi.wasm
  (type $t0 (func (param i32 i32 i32)))
  (type $t1 (func (param i32 i32 i32) (result i32)))
  (type $t2 (func (param i32 i32) (result i32)))
  (type $t3 (func (param i32 i32)))
  (type $t4 (func (param i64) (result i64)))
  (type $t5 (func (param i64 i64 i64 i64) (result i64)))
  (type $t6 (func (param i64 i64) (result i64)))
  (type $t7 (func (param i32 i32 i32 i32)))
  (type $t8 (func (param i32 i32 i32 i32 i32)))
  (type $t9 (func (param i32)))
  (type $t10 (func))
  (type $t11 (func (param i32 i32 i32 i32) (result i32)))
  (import "b" "8" (func $_ZN17soroban_env_guest5guest3buf9bytes_len17h33ae5203a3725b7cE (type $t4)))
  (import "b" "1" (func $_ZN17soroban_env_guest5guest3buf27bytes_copy_to_linear_memory17h9710db4fe7d9274fE (type $t5)))
  (import "b" "3" (func $_ZN17soroban_env_guest5guest3buf28bytes_new_from_linear_memory17h2c31e35d8130569aE (type $t6)))
  (func $_ZN104_$LT$alloy_sol_types..types..data_type..Uint$LT$_$GT$$u20$as$u20$alloy_sol_types..types..ty..SolType$GT$10detokenize17h284d1544edd056e0E (type $t3) (param $p0 i32) (param $p1 i32)
    (local $l2 i32) (local $l3 i32) (local $l4 i32) (local $l5 i64)
    global.get $__stack_pointer
    i32.const 80
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    i32.const 8
    i32.add
    local.get $p1
    i32.const 0
    i32.const 1048816
    call $_ZN111_$LT$alloy_primitives..bits..fixed..FixedBytes$LT$_$GT$$u20$as$u20$core..ops..index..IndexMut$LT$__IdxT$GT$$GT$9index_mut17h96a19399c6348021E
    local.get $l2
    i32.load offset=12
    local.set $l3
    local.get $l2
    i32.load offset=8
    local.set $l4
    block  ;; label = @1
      loop  ;; label = @2
        local.get $l3
        i32.eqz
        br_if 1 (;@1;)
        local.get $l4
        i32.const 0
        i32.store8
        local.get $l3
        i32.const -1
        i32.add
        local.set $l3
        local.get $l4
        i32.const 1
        i32.add
        local.set $l4
        br 0 (;@2;)
      end
    end
    i32.const 24
    local.set $l3
    local.get $l2
    i32.const 16
    i32.add
    i32.const 24
    i32.add
    local.get $p1
    i32.const 24
    i32.add
    i64.load align=1
    i64.store
    local.get $l2
    i32.const 16
    i32.add
    i32.const 16
    i32.add
    local.get $p1
    i32.const 16
    i32.add
    i64.load align=1
    i64.store
    local.get $l2
    i32.const 16
    i32.add
    i32.const 8
    i32.add
    local.get $p1
    i32.const 8
    i32.add
    i64.load align=1
    i64.store
    local.get $l2
    local.get $p1
    i64.load align=1
    i64.store offset=16
    local.get $l2
    i32.const 48
    i32.add
    i32.const 24
    i32.add
    i64.const 0
    i64.store
    local.get $l2
    i32.const 48
    i32.add
    i32.const 16
    i32.add
    i64.const 0
    i64.store
    local.get $l2
    i32.const 48
    i32.add
    i32.const 8
    i32.add
    i64.const 0
    i64.store
    local.get $l2
    i64.const 0
    i64.store offset=48
    local.get $l2
    i32.const 48
    i32.add
    local.set $l4
    block  ;; label = @1
      loop  ;; label = @2
        local.get $l3
        i32.const -8
        i32.eq
        br_if 1 (;@1;)
        local.get $l4
        local.get $l2
        i32.const 16
        i32.add
        local.get $l3
        i32.add
        i64.load align=1
        local.tee $l5
        i64.const 56
        i64.shl
        local.get $l5
        i64.const 65280
        i64.and
        i64.const 40
        i64.shl
        i64.or
        local.get $l5
        i64.const 16711680
        i64.and
        i64.const 24
        i64.shl
        local.get $l5
        i64.const 4278190080
        i64.and
        i64.const 8
        i64.shl
        i64.or
        i64.or
        local.get $l5
        i64.const 8
        i64.shr_u
        i64.const 4278190080
        i64.and
        local.get $l5
        i64.const 24
        i64.shr_u
        i64.const 16711680
        i64.and
        i64.or
        local.get $l5
        i64.const 40
        i64.shr_u
        i64.const 65280
        i64.and
        local.get $l5
        i64.const 56
        i64.shr_u
        i64.or
        i64.or
        i64.or
        i64.store
        local.get $l4
        i32.const 8
        i32.add
        local.set $l4
        local.get $l3
        i32.const -8
        i32.add
        local.set $l3
        br 0 (;@2;)
      end
    end
    local.get $p0
    local.get $l2
    i64.load offset=48
    i64.store
    local.get $p0
    i32.const 24
    i32.add
    local.get $l2
    i32.const 48
    i32.add
    i32.const 24
    i32.add
    i64.load
    i64.store
    local.get $p0
    i32.const 16
    i32.add
    local.get $l2
    i32.const 48
    i32.add
    i32.const 16
    i32.add
    i64.load
    i64.store
    local.get $p0
    i32.const 8
    i32.add
    local.get $l2
    i32.const 48
    i32.add
    i32.const 8
    i32.add
    i64.load
    i64.store
    local.get $l2
    i32.const 80
    i32.add
    global.set $__stack_pointer)
  (func $_ZN111_$LT$alloy_primitives..bits..fixed..FixedBytes$LT$_$GT$$u20$as$u20$core..ops..index..IndexMut$LT$__IdxT$GT$$GT$9index_mut17h96a19399c6348021E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32)
    (local $l4 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l4
    global.set $__stack_pointer
    local.get $l4
    i32.const 8
    i32.add
    local.get $p2
    local.get $p1
    i32.const 32
    local.get $p3
    call $_ZN108_$LT$core..ops..range..RangeTo$LT$usize$GT$$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$9index_mut17hd6d8be024ccdb635E
    local.get $l4
    i32.load offset=12
    local.set $p3
    local.get $p0
    local.get $l4
    i32.load offset=8
    i32.store
    local.get $p0
    local.get $p3
    i32.store offset=4
    local.get $l4
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN108_$LT$core..ops..range..RangeTo$LT$usize$GT$$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$9index_mut17hd6d8be024ccdb635E (type $t8) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (param $p4 i32)
    block  ;; label = @1
      local.get $p1
      local.get $p3
      i32.le_u
      br_if 0 (;@1;)
      local.get $p1
      local.get $p3
      local.get $p4
      call $_ZN4core5slice5index24slice_end_index_len_fail17hc3371dc9f09bc1d5E
      unreachable
    end
    local.get $p0
    local.get $p1
    i32.store offset=4
    local.get $p0
    local.get $p2
    i32.store)
  (func $_ZN4core5slice5index24slice_end_index_len_fail17hc3371dc9f09bc1d5E (type $t0) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    (local $l3 i32) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    local.get $l3
    local.get $p0
    i32.store
    local.get $l3
    local.get $p1
    i32.store offset=4
    local.get $l3
    i32.const 2
    i32.store offset=12
    local.get $l3
    i32.const 1049612
    i32.store offset=8
    local.get $l3
    i64.const 2
    i64.store offset=20 align=4
    local.get $l3
    i32.const 1
    i64.extend_i32_u
    i64.const 32
    i64.shl
    local.tee $l4
    local.get $l3
    i32.const 4
    i32.add
    i64.extend_i32_u
    i64.or
    i64.store offset=40
    local.get $l3
    local.get $l4
    local.get $l3
    i64.extend_i32_u
    i64.or
    i64.store offset=32
    local.get $l3
    local.get $l3
    i32.const 32
    i32.add
    i32.store offset=16
    local.get $l3
    i32.const 8
    i32.add
    local.get $p2
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core3ptr51drop_in_place$LT$alloy_sol_types..errors..Error$GT$17h216e21ed6b1cdbccE (type $t9) (param $p0 i32)
    (local $l1 i32)
    block  ;; label = @1
      local.get $p0
      i32.load
      local.tee $l1
      i32.const -2147483647
      i32.add
      i32.const 0
      local.get $l1
      i32.const -2147483638
      i32.lt_s
      select
      i32.const 7
      i32.ne
      br_if 0 (;@1;)
      local.get $p0
      i32.load offset=12
      local.tee $p0
      i32.const 24
      i32.add
      local.get $p0
      i32.load offset=16
      local.get $p0
      i32.load offset=20
      local.get $p0
      i32.load offset=12
      i32.load offset=8
      call_indirect $T0 (type $t0)
    end)
  (func $_ZN67_$LT$core..array..TryFromSliceError$u20$as$u20$core..fmt..Debug$GT$3fmt17h9039b1fe08508b23E (type $t2) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32) (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32) (local $l7 i32)
    global.get $__stack_pointer
    i32.const 64
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    i32.const 1
    local.set $l3
    block  ;; label = @1
      local.get $p1
      i32.load offset=20
      local.tee $l4
      i32.const 1049071
      i32.const 17
      local.get $p1
      i32.load offset=24
      local.tee $l5
      i32.load offset=12
      local.tee $l6
      call_indirect $T0 (type $t1)
      br_if 0 (;@1;)
      block  ;; label = @2
        block  ;; label = @3
          local.get $p1
          i32.load offset=28
          local.tee $l7
          i32.const 4
          i32.and
          br_if 0 (;@3;)
          i32.const 1
          local.set $l3
          local.get $l4
          i32.const 1049358
          i32.const 1
          local.get $l6
          call_indirect $T0 (type $t1)
          br_if 2 (;@1;)
          local.get $p1
          i32.const 1049188
          i32.const 2
          call $_ZN4core3fmt9Formatter3pad17hdad3e25ba05328b0E
          i32.eqz
          br_if 1 (;@2;)
          br 2 (;@1;)
        end
        local.get $l4
        i32.const 1049359
        i32.const 2
        local.get $l6
        call_indirect $T0 (type $t1)
        br_if 1 (;@1;)
        i32.const 1
        local.set $l3
        local.get $l2
        i32.const 1
        i32.store8 offset=27
        local.get $l2
        local.get $l5
        i32.store offset=16
        local.get $l2
        local.get $l4
        i32.store offset=12
        local.get $l2
        local.get $l7
        i32.store offset=56
        local.get $l2
        i32.const 1049328
        i32.store offset=52
        local.get $l2
        local.get $p1
        i32.load8_u offset=32
        i32.store8 offset=60
        local.get $l2
        local.get $p1
        i32.load offset=16
        i32.store offset=44
        local.get $l2
        local.get $p1
        i64.load offset=8 align=4
        i64.store offset=36 align=4
        local.get $l2
        local.get $p1
        i64.load align=4
        i64.store offset=28 align=4
        local.get $l2
        local.get $l2
        i32.const 27
        i32.add
        i32.store offset=20
        local.get $l2
        local.get $l2
        i32.const 12
        i32.add
        i32.store offset=48
        local.get $l2
        i32.const 28
        i32.add
        i32.const 1049188
        i32.const 2
        call $_ZN4core3fmt9Formatter3pad17hdad3e25ba05328b0E
        br_if 1 (;@1;)
        local.get $l2
        i32.const 12
        i32.add
        i32.const 1049356
        i32.const 2
        call $_ZN68_$LT$core..fmt..builders..PadAdapter$u20$as$u20$core..fmt..Write$GT$9write_str17hf46b591acfd1be0dE
        br_if 1 (;@1;)
      end
      local.get $l4
      i32.const 1049272
      i32.const 1
      local.get $l6
      call_indirect $T0 (type $t1)
      local.set $l3
    end
    local.get $l2
    i32.const 64
    i32.add
    global.set $__stack_pointer
    local.get $l3)
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
          call_indirect $T0 (type $t2)
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
          call_indirect $T0 (type $t2)
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
  (func $_ZN68_$LT$core..fmt..builders..PadAdapter$u20$as$u20$core..fmt..Write$GT$9write_str17hf46b591acfd1be0dE (type $t1) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
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
        i32.const 1049352
        i32.const 4
        local.get $l4
        i32.load offset=12
        call_indirect $T0 (type $t1)
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
      call_indirect $T0 (type $t1)
      local.tee $p0
      local.get $l9
      i32.or
      i32.eqz
      br_if 0 (;@1;)
    end
    local.get $p0)
  (func $_ZN93_$LT$alloy_sol_types..abi..token..WordToken$u20$as$u20$alloy_sol_types..abi..token..Token$GT$11decode_from17h4d1f2d92dc9cf823E (type $t3) (param $p0 i32) (param $p1 i32)
    (local $l2 i32) (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        local.get $p1
        i32.load offset=8
        local.tee $l3
        i32.const 32
        i32.add
        local.tee $l4
        local.get $l3
        i32.lt_u
        br_if 0 (;@2;)
        local.get $p1
        i32.load
        local.set $l5
        local.get $p1
        i32.load offset=4
        local.set $l6
        local.get $l2
        i32.const -2147483648
        i32.store offset=8
        block  ;; label = @3
          block  ;; label = @4
            local.get $l6
            local.get $l4
            i32.lt_u
            br_if 0 (;@4;)
            local.get $l2
            i32.const 8
            i32.add
            call $_ZN4core3ptr51drop_in_place$LT$alloy_sol_types..errors..Error$GT$17h216e21ed6b1cdbccE
            local.get $l4
            local.get $l3
            i32.sub
            i32.const 32
            i32.ne
            br_if 3 (;@1;)
            local.get $p1
            local.get $l4
            i32.store offset=8
            local.get $p0
            local.get $l5
            local.get $l3
            i32.add
            local.tee $p1
            i32.load16_u align=1
            i32.store16 offset=1 align=1
            local.get $p0
            local.get $p1
            i32.load offset=27 align=1
            i32.store offset=28 align=1
            local.get $p0
            local.get $p1
            i64.load offset=3 align=1
            i64.store offset=4 align=4
            local.get $p0
            local.get $p1
            i64.load offset=11 align=1
            i64.store offset=12 align=1
            local.get $p0
            i32.const 3
            i32.add
            local.get $p1
            i32.const 2
            i32.add
            i32.load8_u
            i32.store8
            local.get $p0
            i32.const 32
            i32.add
            local.get $p1
            i32.const 31
            i32.add
            i32.load8_u
            i32.store8
            local.get $p0
            i32.const 20
            i32.add
            local.get $p1
            i32.const 19
            i32.add
            i64.load align=1
            i64.store align=1
            i32.const 0
            local.set $p1
            br 1 (;@3;)
          end
          local.get $p0
          i32.const -2147483648
          i32.store offset=4
          i32.const 1
          local.set $p1
        end
        local.get $p0
        local.get $p1
        i32.store8
        local.get $l2
        i32.const 32
        i32.add
        global.set $__stack_pointer
        return
      end
      i32.const 1048948
      call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
      unreachable
    end
    local.get $l2
    i32.const 8
    i32.add
    call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
    unreachable)
  (func $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E (type $t9) (param $p0 i32)
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
    i32.const 1049220
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
  (func $_ZN4core6result13unwrap_failed17h472431483d5eea7fE (type $t9) (param $p0 i32)
    (local $l1 i32)
    global.get $__stack_pointer
    i32.const 64
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    i32.const 43
    i32.store offset=12
    local.get $l1
    i32.const 1049028
    i32.store offset=8
    local.get $l1
    i32.const 1049012
    i32.store offset=20
    local.get $l1
    local.get $p0
    i32.store offset=16
    local.get $l1
    i32.const 2
    i32.store offset=28
    local.get $l1
    i32.const 1049312
    i32.store offset=24
    local.get $l1
    i64.const 2
    i64.store offset=36 align=4
    local.get $l1
    i32.const 2
    i64.extend_i32_u
    i64.const 32
    i64.shl
    local.get $l1
    i32.const 16
    i32.add
    i64.extend_i32_u
    i64.or
    i64.store offset=56
    local.get $l1
    i32.const 3
    i64.extend_i32_u
    i64.const 32
    i64.shl
    local.get $l1
    i32.const 8
    i32.add
    i64.extend_i32_u
    i64.or
    i64.store offset=48
    local.get $l1
    local.get $l1
    i32.const 48
    i32.add
    i32.store offset=32
    local.get $l1
    i32.const 24
    i32.add
    i32.const 1048964
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN93_$LT$alloy_sol_types..abi..token..WordToken$u20$as$u20$alloy_sol_types..abi..token..Token$GT$11head_append17hc5a6eb2a8a5af8a9E (type $t3) (param $p0 i32) (param $p1 i32)
    (local $l2 i32)
    block  ;; label = @1
      local.get $p1
      i32.load offset=8
      local.tee $l2
      local.get $p1
      i32.load
      i32.ne
      br_if 0 (;@1;)
      local.get $p1
      call $_ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$8grow_one17h2e1c089a719da0cfE
    end
    local.get $p1
    local.get $l2
    i32.const 1
    i32.add
    i32.store offset=8
    local.get $p1
    i32.load offset=4
    local.get $l2
    i32.const 5
    i32.shl
    i32.add
    local.tee $p1
    local.get $p0
    i64.load align=1
    i64.store align=1
    local.get $p1
    i32.const 8
    i32.add
    local.get $p0
    i32.const 8
    i32.add
    i64.load align=1
    i64.store align=1
    local.get $p1
    i32.const 16
    i32.add
    local.get $p0
    i32.const 16
    i32.add
    i64.load align=1
    i64.store align=1
    local.get $p1
    i32.const 24
    i32.add
    local.get $p0
    i32.const 24
    i32.add
    i64.load align=1
    i64.store align=1)
  (func $_ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$8grow_one17h2e1c089a719da0cfE (type $t9) (param $p0 i32)
    (local $l1 i32) (local $l2 i32) (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p0
          i32.load
          local.tee $l2
          i32.const -1
          i32.ne
          br_if 0 (;@3;)
          i32.const 0
          local.set $l1
          br 1 (;@2;)
        end
        i32.const 1
        local.set $l3
        local.get $l2
        i32.const 1
        i32.shl
        local.tee $l4
        local.get $l2
        i32.const 1
        i32.add
        local.tee $l5
        local.get $l4
        local.get $l5
        i32.gt_u
        select
        local.tee $l4
        i32.const 4
        local.get $l4
        i32.const 4
        i32.gt_u
        select
        local.tee $l6
        i32.const 5
        i32.shl
        local.set $l5
        local.get $l4
        i32.const 67108864
        i32.lt_u
        local.set $l4
        block  ;; label = @3
          block  ;; label = @4
            local.get $l2
            br_if 0 (;@4;)
            i32.const 0
            local.set $l3
            br 1 (;@3;)
          end
          local.get $l1
          local.get $l2
          i32.const 5
          i32.shl
          i32.store offset=28
          local.get $l1
          local.get $p0
          i32.load offset=4
          i32.store offset=20
        end
        local.get $l1
        local.get $l3
        i32.store offset=24
        local.get $l1
        i32.const 8
        i32.add
        local.get $l4
        local.get $l5
        local.get $l1
        i32.const 20
        i32.add
        call $_ZN5alloc7raw_vec11finish_grow17h952908d6594349a5E
        local.get $l1
        i32.load offset=8
        i32.eqz
        br_if 1 (;@1;)
        local.get $l1
        i32.load offset=16
        local.set $l2
        local.get $l1
        i32.load offset=12
        local.set $l1
      end
      local.get $l1
      local.get $l2
      call $_ZN5alloc7raw_vec12handle_error17h76131d670f53a5eeE
      unreachable
    end
    local.get $l1
    i32.load offset=12
    local.set $l2
    local.get $p0
    local.get $l6
    i32.store
    local.get $p0
    local.get $l2
    i32.store offset=4
    local.get $l1
    i32.const 32
    i32.add
    global.set $__stack_pointer)
  (func $exec (type $t4) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i32) (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32) (local $l7 i32) (local $l8 i32) (local $l9 i64) (local $l10 i64)
    global.get $__stack_pointer
    i32.const 1184
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              block  ;; label = @6
                block  ;; label = @7
                  local.get $p0
                  i64.const 255
                  i64.and
                  i64.const 72
                  i64.ne
                  br_if 0 (;@7;)
                  local.get $l1
                  i32.const 16
                  i32.add
                  i32.const 0
                  i32.const 128
                  call $memset
                  drop
                  local.get $l1
                  i32.const 8
                  i32.add
                  local.get $p0
                  call $_ZN17soroban_env_guest5guest3buf9bytes_len17h33ae5203a3725b7cE
                  i64.const 32
                  i64.shr_u
                  i32.wrap_i64
                  local.get $l1
                  i32.const 16
                  i32.add
                  i32.const 128
                  i32.const 1049100
                  call $_ZN108_$LT$core..ops..range..RangeTo$LT$usize$GT$$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$9index_mut17hd6d8be024ccdb635E
                  local.get $l1
                  i32.load offset=8
                  local.set $l2
                  local.get $l1
                  i32.load offset=12
                  local.tee $l3
                  local.get $p0
                  call $_ZN17soroban_env_guest5guest3buf9bytes_len17h33ae5203a3725b7cE
                  i64.const 32
                  i64.shr_u
                  i32.wrap_i64
                  i32.ne
                  br_if 1 (;@6;)
                  local.get $p0
                  i64.const 4
                  local.get $l2
                  i64.extend_i32_u
                  i64.const 32
                  i64.shl
                  i64.const 4
                  i64.or
                  local.get $l3
                  i64.extend_i32_u
                  i64.const 32
                  i64.shl
                  i64.const 4
                  i64.or
                  call $_ZN17soroban_env_guest5guest3buf27bytes_copy_to_linear_memory17h9710db4fe7d9274fE
                  drop
                  local.get $l1
                  i32.const 0
                  i32.store offset=744
                  local.get $l1
                  local.get $l3
                  i32.store offset=740
                  local.get $l1
                  local.get $l2
                  i32.store offset=736
                  local.get $l1
                  i32.const 0
                  i32.store16 offset=748
                  local.get $l1
                  i32.const 752
                  i32.add
                  local.get $l1
                  i32.const 736
                  i32.add
                  call $_ZN93_$LT$alloy_sol_types..abi..token..WordToken$u20$as$u20$alloy_sol_types..abi..token..Token$GT$11decode_from17h4d1f2d92dc9cf823E
                  block  ;; label = @8
                    local.get $l1
                    i32.load8_u offset=752
                    br_if 0 (;@8;)
                    local.get $l1
                    i32.const 788
                    i32.add
                    local.get $l1
                    i32.const 736
                    i32.add
                    call $_ZN93_$LT$alloy_sol_types..abi..token..WordToken$u20$as$u20$alloy_sol_types..abi..token..Token$GT$11decode_from17h4d1f2d92dc9cf823E
                    local.get $l1
                    i32.load8_u offset=788
                    br_if 3 (;@5;)
                    local.get $l1
                    i32.const 824
                    i32.add
                    local.get $l1
                    i32.const 736
                    i32.add
                    call $_ZN93_$LT$alloy_sol_types..abi..token..WordToken$u20$as$u20$alloy_sol_types..abi..token..Token$GT$11decode_from17h4d1f2d92dc9cf823E
                    block  ;; label = @9
                      local.get $l1
                      i32.load8_u offset=824
                      i32.eqz
                      br_if 0 (;@9;)
                      local.get $l1
                      i32.const 1075
                      i32.add
                      local.get $l1
                      i32.const 844
                      i32.add
                      i64.load align=4
                      i64.store align=1
                      local.get $l1
                      i32.const 1067
                      i32.add
                      local.get $l1
                      i32.const 836
                      i32.add
                      i64.load align=4
                      i64.store align=1
                      local.get $l1
                      local.get $l1
                      i64.load offset=828 align=4
                      i64.store offset=1059 align=1
                      br 7 (;@2;)
                    end
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 88
                    i32.add
                    local.tee $l3
                    local.get $l1
                    i32.const 824
                    i32.add
                    i32.const 25
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 80
                    i32.add
                    local.tee $l4
                    local.get $l1
                    i32.const 824
                    i32.add
                    i32.const 17
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 72
                    i32.add
                    local.tee $l5
                    local.get $l1
                    i32.const 824
                    i32.add
                    i32.const 9
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 8
                    i32.add
                    local.get $l1
                    i32.const 752
                    i32.add
                    i32.const 1
                    i32.or
                    local.tee $l2
                    i32.const 8
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 16
                    i32.add
                    local.get $l2
                    i32.const 16
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 24
                    i32.add
                    local.get $l2
                    i32.const 24
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 40
                    i32.add
                    local.tee $l6
                    local.get $l1
                    i32.const 788
                    i32.add
                    i32.const 9
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 48
                    i32.add
                    local.tee $l7
                    local.get $l1
                    i32.const 788
                    i32.add
                    i32.const 17
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 56
                    i32.add
                    local.tee $l8
                    local.get $l1
                    i32.const 788
                    i32.add
                    i32.const 25
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    local.get $l1
                    i64.load offset=825 align=1
                    i64.store offset=1120
                    local.get $l1
                    local.get $l1
                    i64.load offset=789 align=1
                    i64.store offset=1088
                    local.get $l1
                    local.get $l2
                    i64.load align=1
                    i64.store offset=1056
                    local.get $l1
                    i32.const 960
                    i32.add
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 96
                    call $memcpy
                    drop
                    local.get $l1
                    i32.const 864
                    i32.add
                    local.get $l1
                    i32.const 960
                    i32.add
                    i32.const 96
                    call $memcpy
                    drop
                    local.get $l1
                    i32.const 640
                    i32.add
                    local.get $l1
                    i32.const 864
                    i32.add
                    i32.const 96
                    call $memcpy
                    drop
                    local.get $l1
                    i32.const 544
                    i32.add
                    local.get $l1
                    i32.const 640
                    i32.add
                    i32.const 96
                    call $memcpy
                    drop
                    local.get $l1
                    i32.const 864
                    i32.add
                    local.get $l1
                    i32.const 544
                    i32.add
                    i32.const 96
                    call $memcpy
                    drop
                    local.get $l1
                    i32.const 640
                    i32.add
                    i32.const 8
                    i32.add
                    local.get $l1
                    i32.const 864
                    i32.add
                    i32.const 72
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 640
                    i32.add
                    i32.const 16
                    i32.add
                    local.get $l1
                    i32.const 864
                    i32.add
                    i32.const 80
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 640
                    i32.add
                    i32.const 24
                    i32.add
                    local.get $l1
                    i32.const 864
                    i32.add
                    i32.const 88
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 824
                    i32.add
                    i32.const 24
                    i32.add
                    local.get $l1
                    i32.const 864
                    i32.add
                    i32.const 56
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 824
                    i32.add
                    i32.const 16
                    i32.add
                    local.get $l1
                    i32.const 864
                    i32.add
                    i32.const 48
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 824
                    i32.add
                    i32.const 8
                    i32.add
                    local.get $l1
                    i32.const 864
                    i32.add
                    i32.const 40
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    local.get $l1
                    i64.load offset=928 align=1
                    i64.store offset=640
                    local.get $l1
                    local.get $l1
                    i64.load offset=896 align=1
                    i64.store offset=824
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 32
                    i32.add
                    local.get $l1
                    i32.const 824
                    i32.add
                    call $_ZN104_$LT$alloy_sol_types..types..data_type..Uint$LT$_$GT$$u20$as$u20$alloy_sol_types..types..ty..SolType$GT$10detokenize17h284d1544edd056e0E
                    local.get $l1
                    i32.const 1120
                    i32.add
                    local.get $l1
                    i32.const 640
                    i32.add
                    call $_ZN104_$LT$alloy_sol_types..types..data_type..Uint$LT$_$GT$$u20$as$u20$alloy_sol_types..types..ty..SolType$GT$10detokenize17h284d1544edd056e0E
                    local.get $l1
                    i32.const 960
                    i32.add
                    i32.const 40
                    i32.add
                    local.get $l6
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 960
                    i32.add
                    i32.const 48
                    i32.add
                    local.get $l7
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 960
                    i32.add
                    i32.const 56
                    i32.add
                    local.get $l8
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 960
                    i32.add
                    i32.const 72
                    i32.add
                    local.get $l5
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 960
                    i32.add
                    i32.const 80
                    i32.add
                    local.get $l4
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 960
                    i32.add
                    i32.const 88
                    i32.add
                    local.get $l3
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 960
                    i32.add
                    i32.const 24
                    i32.add
                    local.get $l1
                    i32.const 544
                    i32.add
                    i32.const 24
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 960
                    i32.add
                    i32.const 16
                    i32.add
                    local.get $l1
                    i32.const 544
                    i32.add
                    i32.const 16
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    i32.const 960
                    i32.add
                    i32.const 8
                    i32.add
                    local.get $l1
                    i32.const 544
                    i32.add
                    i32.const 8
                    i32.add
                    i64.load align=1
                    i64.store
                    local.get $l1
                    local.get $l1
                    i64.load offset=1088
                    i64.store offset=992
                    local.get $l1
                    local.get $l1
                    i64.load offset=1120
                    i64.store offset=1024
                    local.get $l1
                    local.get $l1
                    i64.load offset=544 align=1
                    i64.store offset=960
                    local.get $l1
                    i32.const 144
                    i32.add
                    local.get $l1
                    i32.const 240
                    i32.add
                    i32.const 4
                    i32.or
                    local.get $l1
                    i32.const 440
                    i32.add
                    i32.const 4
                    i32.or
                    local.get $l1
                    i32.const 960
                    i32.add
                    i32.const 96
                    call $memcpy
                    i32.const 96
                    call $memcpy
                    i32.const 96
                    call $memcpy
                    drop
                    local.get $l1
                    i32.const 344
                    i32.add
                    i32.const 8
                    i32.add
                    local.get $l1
                    i32.const 144
                    i32.add
                    i32.const 8
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 344
                    i32.add
                    i32.const 16
                    i32.add
                    local.get $l1
                    i32.const 144
                    i32.add
                    i32.const 16
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 344
                    i32.add
                    i32.const 24
                    i32.add
                    local.get $l1
                    i32.const 144
                    i32.add
                    i32.const 24
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 376
                    i32.add
                    i32.const 8
                    i32.add
                    local.get $l1
                    i32.const 144
                    i32.add
                    i32.const 40
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 376
                    i32.add
                    i32.const 16
                    i32.add
                    local.get $l1
                    i32.const 144
                    i32.add
                    i32.const 48
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 376
                    i32.add
                    i32.const 24
                    i32.add
                    local.get $l1
                    i32.const 144
                    i32.add
                    i32.const 56
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 408
                    i32.add
                    i32.const 8
                    i32.add
                    local.get $l1
                    i32.const 144
                    i32.add
                    i32.const 72
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 408
                    i32.add
                    i32.const 16
                    i32.add
                    local.get $l1
                    i32.const 144
                    i32.add
                    i32.const 80
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 408
                    i32.add
                    i32.const 24
                    i32.add
                    local.get $l1
                    i32.const 144
                    i32.add
                    i32.const 88
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    local.get $l1
                    i64.load offset=144
                    i64.store offset=344
                    local.get $l1
                    local.get $l1
                    i64.load offset=176
                    i64.store offset=376
                    local.get $l1
                    local.get $l1
                    i64.load offset=208
                    i64.store offset=408
                    i32.const 0
                    local.set $l2
                    i64.const 0
                    local.set $p0
                    block  ;; label = @9
                      loop  ;; label = @10
                        local.get $l2
                        i32.const 32
                        i32.eq
                        br_if 1 (;@9;)
                        local.get $l1
                        i32.const 376
                        i32.add
                        local.get $l2
                        i32.add
                        local.tee $l3
                        local.get $p0
                        local.get $l3
                        i64.load
                        i64.add
                        local.tee $l9
                        local.get $l1
                        i32.const 408
                        i32.add
                        local.get $l2
                        i32.add
                        i64.load
                        i64.add
                        local.tee $l10
                        i64.store
                        i64.const 0
                        local.get $l9
                        local.get $p0
                        i64.lt_u
                        i64.extend_i32_u
                        i64.add
                        local.get $l10
                        local.get $l9
                        i64.lt_u
                        i64.extend_i32_u
                        i64.add
                        local.set $p0
                        local.get $l2
                        i32.const 8
                        i32.add
                        local.set $l2
                        br 0 (;@10;)
                      end
                    end
                    local.get $l1
                    i32.const 240
                    i32.add
                    i32.const 24
                    i32.add
                    local.get $l1
                    i32.const 344
                    i32.add
                    i32.const 24
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 240
                    i32.add
                    i32.const 16
                    i32.add
                    local.get $l1
                    i32.const 344
                    i32.add
                    i32.const 16
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 240
                    i32.add
                    i32.const 8
                    i32.add
                    local.get $l1
                    i32.const 344
                    i32.add
                    i32.const 8
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 280
                    i32.add
                    local.tee $l2
                    local.get $l1
                    i32.const 376
                    i32.add
                    i32.const 8
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 288
                    i32.add
                    local.tee $l3
                    local.get $l1
                    i32.const 376
                    i32.add
                    i32.const 16
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 296
                    i32.add
                    local.tee $l4
                    local.get $l1
                    i32.const 376
                    i32.add
                    i32.const 24
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    local.get $l1
                    i64.load offset=344
                    i64.store offset=240
                    local.get $l1
                    local.get $l1
                    i64.load offset=376
                    i64.store offset=272
                    local.get $l1
                    i32.const 440
                    i32.add
                    i32.const 24
                    i32.add
                    local.tee $l5
                    i64.const 0
                    i64.store
                    local.get $l1
                    i32.const 440
                    i32.add
                    i32.const 16
                    i32.add
                    local.tee $l6
                    i64.const 0
                    i64.store
                    local.get $l1
                    i32.const 440
                    i32.add
                    i32.const 8
                    i32.add
                    local.tee $l7
                    i64.const 0
                    i64.store
                    local.get $l1
                    i64.const 0
                    i64.store offset=440
                    local.get $l1
                    local.get $l1
                    i32.const 440
                    i32.add
                    i32.const 32
                    i32.const 1048980
                    call $_ZN111_$LT$alloy_primitives..bits..fixed..FixedBytes$LT$_$GT$$u20$as$u20$core..ops..index..IndexMut$LT$__IdxT$GT$$GT$9index_mut17h96a19399c6348021E
                    local.get $l1
                    i32.load
                    local.get $l1
                    i32.load offset=4
                    local.get $l1
                    i32.const 240
                    i32.add
                    i32.const 1048996
                    call $_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$15copy_from_slice17h981be368a0b7f816E
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 24
                    i32.add
                    local.get $l5
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 16
                    i32.add
                    local.get $l6
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 8
                    i32.add
                    local.get $l7
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 1152
                    i32.add
                    i32.const 8
                    i32.add
                    local.get $l2
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 1152
                    i32.add
                    i32.const 16
                    i32.add
                    local.get $l3
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 1152
                    i32.add
                    i32.const 24
                    i32.add
                    local.get $l4
                    i64.load
                    i64.store
                    local.get $l1
                    local.get $l1
                    i64.load offset=440
                    i64.store offset=1056
                    local.get $l1
                    local.get $l1
                    i64.load offset=272
                    i64.store offset=1152
                    i32.const 0
                    local.set $l2
                    block  ;; label = @9
                      loop  ;; label = @10
                        local.get $l2
                        i32.const 16
                        i32.eq
                        br_if 1 (;@9;)
                        local.get $l1
                        i32.const 1152
                        i32.add
                        local.get $l2
                        i32.add
                        local.tee $l3
                        i32.load8_u
                        local.set $l4
                        local.get $l3
                        local.get $l1
                        i32.const 1152
                        i32.add
                        local.get $l2
                        i32.const 31
                        i32.xor
                        i32.add
                        local.tee $l5
                        i32.load8_u
                        i32.store8
                        local.get $l5
                        local.get $l4
                        i32.store8
                        local.get $l2
                        i32.const 1
                        i32.add
                        local.set $l2
                        br 0 (;@10;)
                      end
                    end
                    local.get $l1
                    i32.const 496
                    i32.add
                    local.get $l1
                    i32.const 1152
                    i32.add
                    i32.const 24
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 488
                    i32.add
                    local.get $l1
                    i32.const 1152
                    i32.add
                    i32.const 16
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 480
                    i32.add
                    local.get $l1
                    i32.const 1152
                    i32.add
                    i32.const 8
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 440
                    i32.add
                    i32.const 8
                    i32.add
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 8
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 440
                    i32.add
                    i32.const 16
                    i32.add
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 16
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    i32.const 440
                    i32.add
                    i32.const 24
                    i32.add
                    local.get $l1
                    i32.const 1056
                    i32.add
                    i32.const 24
                    i32.add
                    i64.load
                    i64.store
                    local.get $l1
                    local.get $l1
                    i64.load offset=1152
                    i64.store offset=472
                    local.get $l1
                    local.get $l1
                    i64.load offset=1056
                    i64.store offset=440
                    i32.const 1
                    i32.const 64
                    call $_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$8allocate17h5fb8fec45863b9d0E
                    local.tee $l3
                    i32.eqz
                    br_if 4 (;@4;)
                    i32.const 4
                    i32.const 16
                    call $_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$8allocate17h5fb8fec45863b9d0E
                    local.tee $l2
                    i32.eqz
                    br_if 5 (;@3;)
                    local.get $l2
                    i32.const 64
                    i32.store
                    local.get $l1
                    local.get $l2
                    i32.store offset=1072
                    local.get $l1
                    i64.const 17179869184
                    i64.store offset=1064 align=4
                    local.get $l1
                    local.get $l3
                    i32.store offset=1060
                    local.get $l1
                    i32.const 2
                    i32.store offset=1056
                    local.get $l1
                    i32.const 1
                    i32.store offset=1076
                    local.get $l1
                    i32.const 440
                    i32.add
                    local.get $l1
                    i32.const 1056
                    i32.add
                    call $_ZN93_$LT$alloy_sol_types..abi..token..WordToken$u20$as$u20$alloy_sol_types..abi..token..Token$GT$11head_append17hc5a6eb2a8a5af8a9E
                    local.get $l1
                    i32.const 472
                    i32.add
                    local.get $l1
                    i32.const 1056
                    i32.add
                    call $_ZN93_$LT$alloy_sol_types..abi..token..WordToken$u20$as$u20$alloy_sol_types..abi..token..Token$GT$11head_append17hc5a6eb2a8a5af8a9E
                    local.get $l1
                    i64.load32_u offset=1060
                    i64.const 32
                    i64.shl
                    i64.const 4
                    i64.or
                    local.get $l1
                    i64.load32_u offset=1064
                    i64.const 37
                    i64.shl
                    i64.const 4
                    i64.or
                    call $_ZN17soroban_env_guest5guest3buf28bytes_new_from_linear_memory17h2c31e35d8130569aE
                    local.set $p0
                    br 7 (;@1;)
                  end
                  local.get $l1
                  i32.const 1075
                  i32.add
                  local.get $l1
                  i32.const 772
                  i32.add
                  i64.load align=4
                  i64.store align=1
                  local.get $l1
                  i32.const 1067
                  i32.add
                  local.get $l1
                  i32.const 764
                  i32.add
                  i64.load align=4
                  i64.store align=1
                  local.get $l1
                  local.get $l1
                  i64.load offset=756 align=4
                  i64.store offset=1059 align=1
                  br 5 (;@2;)
                end
                unreachable
                unreachable
              end
              call $_ZN11soroban_sdk5bytes5Bytes15copy_into_slice19panic_cold_explicit17h998e75ccf1d2e56aE
              unreachable
            end
            local.get $l1
            i32.const 1075
            i32.add
            local.get $l1
            i32.const 808
            i32.add
            i64.load align=4
            i64.store align=1
            local.get $l1
            i32.const 1067
            i32.add
            local.get $l1
            i32.const 800
            i32.add
            i64.load align=4
            i64.store align=1
            local.get $l1
            local.get $l1
            i64.load offset=792 align=4
            i64.store offset=1059 align=1
            br 2 (;@2;)
          end
          i32.const 1
          i32.const 64
          call $_ZN5alloc7raw_vec12handle_error17h76131d670f53a5eeE
          unreachable
        end
        i32.const 4
        i32.const 16
        call $_ZN5alloc7raw_vec12handle_error17h76131d670f53a5eeE
        unreachable
      end
      local.get $l1
      i32.const 544
      i32.add
      i32.const 19
      i32.add
      local.tee $l2
      local.get $l1
      i32.const 1056
      i32.add
      i32.const 19
      i32.add
      i64.load align=1
      i64.store align=1
      local.get $l1
      i32.const 544
      i32.add
      i32.const 11
      i32.add
      local.tee $l3
      local.get $l1
      i32.const 1056
      i32.add
      i32.const 11
      i32.add
      i64.load align=1
      i64.store align=1
      local.get $l1
      local.get $l1
      i64.load offset=1059 align=1
      local.tee $p0
      i64.store offset=643 align=1
      local.get $l1
      local.get $p0
      i64.store offset=547 align=1
      local.get $l1
      i32.const 440
      i32.add
      i32.const 16
      i32.add
      local.tee $l4
      local.get $l2
      i64.load align=1
      i64.store
      local.get $l1
      i32.const 440
      i32.add
      i32.const 8
      i32.add
      local.tee $l2
      local.get $l3
      i64.load align=1
      i64.store
      local.get $l1
      local.get $l1
      i64.load offset=547 align=1
      i64.store offset=440
      local.get $l1
      i32.const 240
      i32.add
      i32.const 16
      i32.add
      local.get $l4
      i64.load
      i64.store
      local.get $l1
      i32.const 240
      i32.add
      i32.const 8
      i32.add
      local.get $l2
      i64.load
      i64.store
      local.get $l1
      local.get $l1
      i64.load offset=440
      i64.store offset=240
      local.get $l1
      i32.const 240
      i32.add
      call $_ZN4core3ptr51drop_in_place$LT$alloy_sol_types..errors..Error$GT$17h216e21ed6b1cdbccE
      i64.const 4294967299
      local.set $p0
    end
    local.get $l1
    i32.const 1184
    i32.add
    global.set $__stack_pointer
    local.get $p0)
  (func $_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$15copy_from_slice17h981be368a0b7f816E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32)
    block  ;; label = @1
      local.get $p1
      i32.const 32
      i32.ne
      br_if 0 (;@1;)
      local.get $p0
      local.get $p2
      i64.load align=1
      i64.store align=1
      local.get $p0
      i32.const 24
      i32.add
      local.get $p2
      i32.const 24
      i32.add
      i64.load align=1
      i64.store align=1
      local.get $p0
      i32.const 16
      i32.add
      local.get $p2
      i32.const 16
      i32.add
      i64.load align=1
      i64.store align=1
      local.get $p0
      i32.const 8
      i32.add
      local.get $p2
      i32.const 8
      i32.add
      i64.load align=1
      i64.store align=1
      return
    end
    local.get $p1
    local.get $p3
    call $_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$15copy_from_slice17len_mismatch_fail17h1f4168c6dfc810e9E
    unreachable)
  (func $_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$8allocate17h5fb8fec45863b9d0E (type $t2) (param $p0 i32) (param $p1 i32) (result i32)
    i32.const 0
    i32.load8_u offset=1049880
    drop
    local.get $p1
    local.get $p0
    call $__rust_alloc)
  (func $_ZN11soroban_sdk5bytes5Bytes15copy_into_slice19panic_cold_explicit17h998e75ccf1d2e56aE (type $t10)
    i32.const 1048800
    call $_ZN4core9panicking14panic_explicit17h0d32b058017db662E
    unreachable)
  (func $_ZN5alloc7raw_vec12handle_error17h76131d670f53a5eeE (type $t3) (param $p0 i32) (param $p1 i32)
    block  ;; label = @1
      local.get $p0
      br_if 0 (;@1;)
      call $_ZN5alloc7raw_vec17capacity_overflow17h76f9308d7d8b5961E
      unreachable
    end
    unreachable
    unreachable)
  (func $_ZN5alloc7raw_vec17capacity_overflow17h76f9308d7d8b5961E (type $t10)
    (local $l0 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    i32.const 0
    i32.store offset=24
    local.get $l0
    i32.const 1
    i32.store offset=12
    local.get $l0
    i32.const 1049136
    i32.store offset=8
    local.get $l0
    i64.const 4
    i64.store offset=16 align=4
    local.get $l0
    i32.const 8
    i32.add
    i32.const 1049172
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t3) (param $p0 i32) (param $p1 i32)
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
  (func $__rust_alloc (type $t2) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32) (local $l3 i32)
    call $_ZN11soroban_sdk5alloc16BumpPointerLocal10maybe_init17h645f37fb35323fecE
    block  ;; label = @1
      local.get $p1
      i32.const 0
      i32.load offset=1049872
      local.tee $l2
      i32.add
      i32.const -1
      i32.add
      local.tee $l3
      local.get $l2
      i32.lt_u
      br_if 0 (;@1;)
      block  ;; label = @2
        local.get $l3
        i32.const 0
        local.get $p1
        i32.sub
        i32.and
        local.tee $l2
        local.get $p0
        i32.add
        local.tee $l3
        i32.const 0
        i32.load offset=1049876
        i32.le_u
        br_if 0 (;@2;)
        local.get $p0
        local.get $p1
        call $_ZN11soroban_sdk5alloc16BumpPointerLocal10alloc_slow17hcc00c1907fbef2c3E
        return
      end
      i32.const 0
      local.get $l3
      i32.store offset=1049872
      local.get $l2
      return
    end
    i32.const 1049824
    call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
    unreachable)
  (func $_ZN5alloc7raw_vec11finish_grow17h952908d6594349a5E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32)
    (local $l4 i32) (local $l5 i32) (local $l6 i32) (local $l7 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l4
    global.set $__stack_pointer
    i32.const 1
    local.set $l5
    i32.const 0
    local.set $l6
    i32.const 4
    local.set $l7
    block  ;; label = @1
      local.get $p1
      i32.eqz
      br_if 0 (;@1;)
      local.get $p2
      i32.const 0
      i32.lt_s
      br_if 0 (;@1;)
      block  ;; label = @2
        block  ;; label = @3
          local.get $p3
          i32.load offset=4
          i32.eqz
          br_if 0 (;@3;)
          block  ;; label = @4
            local.get $p3
            i32.load offset=8
            local.tee $l6
            br_if 0 (;@4;)
            local.get $l4
            i32.const 8
            i32.add
            local.get $p1
            local.get $p2
            call $_ZN5alloc5alloc6Global10alloc_impl17h937169c39eac7921E.92
            local.get $l4
            i32.load offset=12
            local.set $l6
            local.get $l4
            i32.load offset=8
            local.set $l7
            br 2 (;@2;)
          end
          local.get $p3
          i32.load
          local.get $l6
          local.get $p1
          local.get $p2
          call $__rust_realloc
          local.set $l7
          local.get $p2
          local.set $l6
          br 1 (;@2;)
        end
        local.get $l4
        local.get $p1
        local.get $p2
        call $_ZN5alloc5alloc6Global10alloc_impl17h937169c39eac7921E.92
        local.get $l4
        i32.load offset=4
        local.set $l6
        local.get $l4
        i32.load
        local.set $l7
      end
      block  ;; label = @2
        local.get $l7
        i32.eqz
        br_if 0 (;@2;)
        local.get $p0
        local.get $l7
        i32.store offset=4
        i32.const 0
        local.set $l5
        i32.const 8
        local.set $l7
        br 1 (;@1;)
      end
      local.get $p0
      local.get $p1
      i32.store offset=4
      i32.const 8
      local.set $l7
      local.get $p2
      local.set $l6
    end
    local.get $p0
    local.get $l7
    i32.add
    local.get $l6
    i32.store
    local.get $p0
    local.get $l5
    i32.store
    local.get $l4
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $_ZN5alloc5alloc6Global10alloc_impl17h937169c39eac7921E.92 (type $t0) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    block  ;; label = @1
      local.get $p2
      i32.eqz
      br_if 0 (;@1;)
      i32.const 0
      i32.load8_u offset=1049880
      drop
      local.get $p2
      local.get $p1
      call $__rust_alloc
      local.set $p1
    end
    local.get $p0
    local.get $p2
    i32.store offset=4
    local.get $p0
    local.get $p1
    i32.store)
  (func $__rust_realloc (type $t11) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (result i32)
    (local $l4 i32) (local $l5 i32)
    call $_ZN11soroban_sdk5alloc16BumpPointerLocal10maybe_init17h645f37fb35323fecE
    block  ;; label = @1
      local.get $p2
      i32.const 0
      i32.load offset=1049872
      local.tee $l4
      i32.add
      i32.const -1
      i32.add
      local.tee $l5
      local.get $l4
      i32.lt_u
      br_if 0 (;@1;)
      block  ;; label = @2
        block  ;; label = @3
          local.get $l5
          i32.const 0
          local.get $p2
          i32.sub
          i32.and
          local.tee $l4
          local.get $p3
          i32.add
          local.tee $l5
          i32.const 0
          i32.load offset=1049876
          i32.le_u
          br_if 0 (;@3;)
          local.get $p3
          local.get $p2
          call $_ZN11soroban_sdk5alloc16BumpPointerLocal10alloc_slow17hcc00c1907fbef2c3E
          local.set $l4
          br 1 (;@2;)
        end
        i32.const 0
        local.get $l5
        i32.store offset=1049872
      end
      block  ;; label = @2
        local.get $l4
        i32.eqz
        br_if 0 (;@2;)
        local.get $l4
        local.get $p0
        local.get $p1
        local.get $p3
        local.get $p1
        local.get $p3
        i32.lt_u
        select
        call $memcpy
        drop
      end
      local.get $l4
      return
    end
    i32.const 1049824
    call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
    unreachable)
  (func $rust_begin_unwind (type $t9) (param $p0 i32)
    (local $l1 i32) (local $l2 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $p0
    i32.load offset=24
    local.set $l2
    local.get $l1
    i32.const 16
    i32.add
    local.get $p0
    i32.const 16
    i32.add
    i64.load align=4
    i64.store
    local.get $l1
    i32.const 8
    i32.add
    local.get $p0
    i32.const 8
    i32.add
    i64.load align=4
    i64.store
    local.get $l1
    local.get $p0
    i32.store offset=28
    local.get $l1
    local.get $l2
    i32.store offset=24
    local.get $l1
    local.get $p0
    i64.load align=4
    i64.store
    local.get $l1
    call $_ZN3std3sys9backtrace26__rust_end_short_backtrace17h2bcfc60c3cf0a312E
    unreachable)
  (func $_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u32$GT$3fmt17hd46d69ca3fa9eb1eE (type $t2) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32) (local $l3 i32) (local $l4 i64) (local $l5 i64) (local $l6 i32) (local $l7 i32) (local $l8 i32) (local $l9 i32) (local $l10 i32) (local $l11 i32) (local $l12 i32) (local $l13 i32) (local $l14 i32) (local $l15 i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    i32.const 39
    local.set $l3
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i64.load32_u
        local.tee $l4
        i64.const 10000
        i64.ge_u
        br_if 0 (;@2;)
        local.get $l4
        local.set $l5
        br 1 (;@1;)
      end
      i32.const 39
      local.set $l3
      loop  ;; label = @2
        local.get $l2
        i32.const 9
        i32.add
        local.get $l3
        i32.add
        local.tee $p0
        i32.const -4
        i32.add
        local.get $l4
        i64.const 10000
        i64.div_u
        local.tee $l5
        i64.const 55536
        i64.mul
        local.get $l4
        i64.add
        i32.wrap_i64
        local.tee $l6
        i32.const 65535
        i32.and
        i32.const 100
        i32.div_u
        local.tee $l7
        i32.const 1
        i32.shl
        i32.const 1049361
        i32.add
        i32.load16_u align=1
        i32.store16 align=1
        local.get $p0
        i32.const -2
        i32.add
        local.get $l7
        i32.const -100
        i32.mul
        local.get $l6
        i32.add
        i32.const 65535
        i32.and
        i32.const 1
        i32.shl
        i32.const 1049361
        i32.add
        i32.load16_u align=1
        i32.store16 align=1
        local.get $l3
        i32.const -4
        i32.add
        local.set $l3
        local.get $l4
        i64.const 99999999
        i64.gt_u
        local.set $p0
        local.get $l5
        local.set $l4
        local.get $p0
        br_if 0 (;@2;)
      end
    end
    block  ;; label = @1
      local.get $l5
      i32.wrap_i64
      local.tee $p0
      i32.const 99
      i32.le_u
      br_if 0 (;@1;)
      local.get $l2
      i32.const 9
      i32.add
      local.get $l3
      i32.const -2
      i32.add
      local.tee $l3
      i32.add
      local.get $l5
      i32.wrap_i64
      local.tee $l6
      i32.const 65535
      i32.and
      i32.const 100
      i32.div_u
      local.tee $p0
      i32.const -100
      i32.mul
      local.get $l6
      i32.add
      i32.const 65535
      i32.and
      i32.const 1
      i32.shl
      i32.const 1049361
      i32.add
      i32.load16_u align=1
      i32.store16 align=1
    end
    block  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i32.const 10
        i32.lt_u
        br_if 0 (;@2;)
        local.get $l2
        i32.const 9
        i32.add
        local.get $l3
        i32.const -2
        i32.add
        local.tee $l3
        i32.add
        local.get $p0
        i32.const 1
        i32.shl
        i32.const 1049361
        i32.add
        i32.load16_u align=1
        i32.store16 align=1
        br 1 (;@1;)
      end
      local.get $l2
      i32.const 9
      i32.add
      local.get $l3
      i32.const -1
      i32.add
      local.tee $l3
      i32.add
      local.get $p0
      i32.const 48
      i32.or
      i32.store8
    end
    i32.const 39
    local.get $l3
    i32.sub
    local.set $l8
    i32.const 1
    local.set $l7
    i32.const 43
    i32.const 1114112
    local.get $p1
    i32.load offset=28
    local.tee $p0
    i32.const 1
    i32.and
    local.tee $l6
    select
    local.set $l9
    local.get $p0
    i32.const 4
    i32.and
    i32.const 2
    i32.shr_u
    local.set $l10
    local.get $l2
    i32.const 9
    i32.add
    local.get $l3
    i32.add
    local.set $l11
    block  ;; label = @1
      block  ;; label = @2
        local.get $p1
        i32.load
        br_if 0 (;@2;)
        local.get $p1
        i32.load offset=20
        local.tee $l3
        local.get $p1
        i32.load offset=24
        local.tee $p0
        local.get $l9
        local.get $l10
        call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
        br_if 1 (;@1;)
        local.get $l3
        local.get $l11
        local.get $l8
        local.get $p0
        i32.load offset=12
        call_indirect $T0 (type $t1)
        local.set $l7
        br 1 (;@1;)
      end
      block  ;; label = @2
        local.get $p1
        i32.load offset=4
        local.tee $l12
        local.get $l6
        local.get $l8
        i32.add
        local.tee $l7
        i32.gt_u
        br_if 0 (;@2;)
        i32.const 1
        local.set $l7
        local.get $p1
        i32.load offset=20
        local.tee $l3
        local.get $p1
        i32.load offset=24
        local.tee $p0
        local.get $l9
        local.get $l10
        call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
        br_if 1 (;@1;)
        local.get $l3
        local.get $l11
        local.get $l8
        local.get $p0
        i32.load offset=12
        call_indirect $T0 (type $t1)
        local.set $l7
        br 1 (;@1;)
      end
      block  ;; label = @2
        local.get $p0
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
        local.set $l7
        local.get $p1
        i32.const 1
        i32.store8 offset=32
        local.get $p1
        i32.load offset=20
        local.tee $p0
        local.get $p1
        i32.load offset=24
        local.tee $l15
        local.get $l9
        local.get $l10
        call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
        br_if 1 (;@1;)
        local.get $l3
        local.get $l12
        i32.add
        local.get $l6
        i32.sub
        i32.const -38
        i32.add
        local.set $l3
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l3
            i32.const -1
            i32.add
            local.tee $l3
            i32.eqz
            br_if 1 (;@3;)
            local.get $p0
            i32.const 48
            local.get $l15
            i32.load offset=16
            call_indirect $T0 (type $t2)
            i32.eqz
            br_if 0 (;@4;)
            br 3 (;@1;)
          end
        end
        local.get $p0
        local.get $l11
        local.get $l8
        local.get $l15
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
        local.set $l7
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
            local.tee $l3
            br_table 2 (;@2;) 0 (;@4;) 1 (;@3;) 0 (;@4;) 2 (;@2;)
          end
          local.get $l12
          local.set $l3
          i32.const 0
          local.set $l12
          br 1 (;@2;)
        end
        local.get $l12
        i32.const 1
        i32.shr_u
        local.set $l3
        local.get $l12
        i32.const 1
        i32.add
        i32.const 1
        i32.shr_u
        local.set $l12
      end
      local.get $l3
      i32.const 1
      i32.add
      local.set $l3
      local.get $p1
      i32.load offset=16
      local.set $l15
      local.get $p1
      i32.load offset=24
      local.set $p0
      local.get $p1
      i32.load offset=20
      local.set $l6
      block  ;; label = @2
        loop  ;; label = @3
          local.get $l3
          i32.const -1
          i32.add
          local.tee $l3
          i32.eqz
          br_if 1 (;@2;)
          local.get $l6
          local.get $l15
          local.get $p0
          i32.load offset=16
          call_indirect $T0 (type $t2)
          i32.eqz
          br_if 0 (;@3;)
        end
        i32.const 1
        local.set $l7
        br 1 (;@1;)
      end
      i32.const 1
      local.set $l7
      local.get $l6
      local.get $p0
      local.get $l9
      local.get $l10
      call $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E
      br_if 0 (;@1;)
      local.get $l6
      local.get $l11
      local.get $l8
      local.get $p0
      i32.load offset=12
      call_indirect $T0 (type $t1)
      br_if 0 (;@1;)
      i32.const 0
      local.set $l3
      loop  ;; label = @2
        block  ;; label = @3
          local.get $l12
          local.get $l3
          i32.ne
          br_if 0 (;@3;)
          local.get $l12
          local.get $l12
          i32.lt_u
          local.set $l7
          br 2 (;@1;)
        end
        local.get $l3
        i32.const 1
        i32.add
        local.set $l3
        local.get $l6
        local.get $l15
        local.get $p0
        i32.load offset=16
        call_indirect $T0 (type $t2)
        i32.eqz
        br_if 0 (;@2;)
      end
      local.get $l3
      i32.const -1
      i32.add
      local.get $l12
      i32.lt_u
      local.set $l7
    end
    local.get $l2
    i32.const 48
    i32.add
    global.set $__stack_pointer
    local.get $l7)
  (func $_ZN4core3fmt9Formatter12pad_integral12write_prefix17hd0d96a1c692dec19E (type $t11) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (result i32)
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
          call_indirect $T0 (type $t2)
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
  (func $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17h9634f975d7713204E (type $t2) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p1
    local.get $p0
    i32.load
    local.get $p0
    i32.load offset=4
    call $_ZN4core3fmt9Formatter3pad17hdad3e25ba05328b0E)
  (func $_ZN42_$LT$$RF$T$u20$as$u20$core..fmt..Debug$GT$3fmt17hbd1c3de5eced27c6E (type $t2) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p0
    i32.load
    local.get $p1
    local.get $p0
    i32.load offset=4
    i32.load offset=12
    call_indirect $T0 (type $t2))
  (func $_ZN4core3fmt5write17hbbcd4b328f92d3c5E (type $t1) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
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
                  call_indirect $T0 (type $t1)
                  br_if 4 (;@3;)
                end
                local.get $p1
                i32.load
                local.get $l3
                i32.const 12
                i32.add
                local.get $p1
                i32.load offset=4
                call_indirect $T0 (type $t2)
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
                call_indirect $T0 (type $t1)
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
              call_indirect $T0 (type $t2)
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
          call_indirect $T0 (type $t1)
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
  (func $_ZN68_$LT$core..fmt..builders..PadAdapter$u20$as$u20$core..fmt..Write$GT$10write_char17hdff090ddce8dafe2E (type $t2) (param $p0 i32) (param $p1 i32) (result i32)
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
      i32.const 1049352
      i32.const 4
      local.get $l2
      i32.load offset=12
      call_indirect $T0 (type $t1)
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
    call_indirect $T0 (type $t2))
  (func $_ZN4core3fmt5Write9write_fmt17h07171b83fe780f81E (type $t2) (param $p0 i32) (param $p1 i32) (result i32)
    local.get $p0
    i32.const 1049328
    local.get $p1
    call $_ZN4core3fmt5write17hbbcd4b328f92d3c5E)
  (func $_ZN4core9panicking14panic_explicit17h0d32b058017db662E (type $t9) (param $p0 i32)
    (local $l1 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $l1
    i32.const 1
    i32.store offset=4
    local.get $l1
    i32.const 1049276
    i32.store
    local.get $l1
    i64.const 1
    i64.store offset=12 align=4
    local.get $l1
    i32.const 3
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i32.const 1049300
    i64.extend_i32_u
    i64.or
    i64.store offset=24
    local.get $l1
    local.get $l1
    i32.const 24
    i32.add
    i32.store offset=8
    local.get $l1
    local.get $p0
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$15copy_from_slice17len_mismatch_fail17h1f4168c6dfc810e9E (type $t3) (param $p0 i32) (param $p1 i32)
    (local $l2 i32) (local $l3 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l2
    global.set $__stack_pointer
    local.get $l2
    i32.const 32
    i32.store offset=4
    local.get $l2
    local.get $p0
    i32.store
    local.get $l2
    i32.const 3
    i32.store offset=12
    local.get $l2
    i32.const 1049692
    i32.store offset=8
    local.get $l2
    i64.const 2
    i64.store offset=20 align=4
    local.get $l2
    i32.const 1
    i64.extend_i32_u
    i64.const 32
    i64.shl
    local.tee $l3
    local.get $l2
    i64.extend_i32_u
    i64.or
    i64.store offset=40
    local.get $l2
    local.get $l3
    local.get $l2
    i32.const 4
    i32.add
    i64.extend_i32_u
    i64.or
    i64.store offset=32
    local.get $l2
    local.get $l2
    i32.const 32
    i32.add
    i32.store offset=16
    local.get $l2
    i32.const 8
    i32.add
    local.get $p1
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core9panicking11panic_const24panic_const_mul_overflow17hfc625200574f06ecE (type $t10)
    (local $l0 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    i32.const 0
    i32.store offset=24
    local.get $l0
    i32.const 1
    i32.store offset=12
    local.get $l0
    i32.const 1049264
    i32.store offset=8
    local.get $l0
    i64.const 4
    i64.store offset=16 align=4
    local.get $l0
    i32.const 8
    i32.add
    i32.const 1049840
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN11soroban_sdk5alloc16BumpPointerLocal10maybe_init17h645f37fb35323fecE (type $t10)
    (local $l0 i32)
    block  ;; label = @1
      block  ;; label = @2
        i32.const 0
        i32.load offset=1049876
        br_if 0 (;@2;)
        memory.size
        local.tee $l0
        i32.const 65535
        i32.gt_u
        br_if 1 (;@1;)
        i32.const 0
        local.get $l0
        i32.const 16
        i32.shl
        local.tee $l0
        i32.store offset=1049876
        i32.const 0
        local.get $l0
        i32.store offset=1049872
      end
      return
    end
    call $_ZN4core9panicking11panic_const24panic_const_mul_overflow17hfc625200574f06ecE
    unreachable)
  (func $_ZN11soroban_sdk5alloc16BumpPointerLocal10alloc_slow17hcc00c1907fbef2c3E (type $t2) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32) (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32)
    i32.const 0
    local.get $p1
    i32.sub
    local.set $l2
    local.get $p1
    i32.const -1
    i32.add
    local.set $l3
    local.get $p0
    i32.const 65535
    i32.add
    local.tee $p1
    i32.const -65536
    i32.and
    local.set $l4
    local.get $p1
    i32.const 16
    i32.shr_u
    local.set $l5
    block  ;; label = @1
      block  ;; label = @2
        loop  ;; label = @3
          local.get $l5
          memory.grow
          i32.const -1
          i32.eq
          br_if 1 (;@2;)
          i32.const 0
          i32.const 0
          i32.load offset=1049876
          local.get $l4
          i32.add
          i32.store offset=1049876
          call $_ZN11soroban_sdk5alloc16BumpPointerLocal10maybe_init17h645f37fb35323fecE
          i32.const 0
          i32.load offset=1049872
          local.tee $p1
          local.get $l3
          i32.add
          local.tee $l6
          local.get $p1
          i32.lt_u
          br_if 2 (;@1;)
          local.get $l6
          local.get $l2
          i32.and
          local.tee $p1
          local.get $p0
          i32.add
          local.tee $l6
          i32.const 0
          i32.load offset=1049876
          i32.gt_u
          br_if 0 (;@3;)
        end
        i32.const 0
        local.get $l6
        i32.store offset=1049872
        local.get $p1
        return
      end
      call $_ZN11soroban_sdk5alloc16BumpPointerLocal17alloc_slow_inline19panic_cold_explicit17h1d54ddddbf6d9eccE
      unreachable
    end
    i32.const 1049824
    call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
    unreachable)
  (func $_ZN11soroban_sdk5alloc16BumpPointerLocal17alloc_slow_inline19panic_cold_explicit17h1d54ddddbf6d9eccE (type $t10)
    i32.const 1049856
    call $_ZN4core9panicking14panic_explicit17h0d32b058017db662E
    unreachable)
  (func $_ (type $t10))
  (func $rust_panic (type $t10)
    unreachable
    unreachable)
  (func $_ZN4core5panic12PanicPayload6as_str17h59025c0ecbb0f54eE (type $t3) (param $p0 i32) (param $p1 i32)
    local.get $p0
    i32.const 0
    i32.store)
  (func $_ZN3std3sys9backtrace26__rust_end_short_backtrace17h2bcfc60c3cf0a312E (type $t9) (param $p0 i32)
    local.get $p0
    call $_ZN3std9panicking19begin_panic_handler28_$u7b$$u7b$closure$u7d$$u7d$17h98de848d678bad07E
    unreachable)
  (func $_ZN3std9panicking19begin_panic_handler28_$u7b$$u7b$closure$u7d$$u7d$17h98de848d678bad07E (type $t9) (param $p0 i32)
    (local $l1 i32) (local $l2 i32) (local $l3 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $p0
    i32.load offset=12
    local.set $l2
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          block  ;; label = @4
            local.get $p0
            i32.load offset=4
            br_table 0 (;@4;) 1 (;@3;) 2 (;@2;)
          end
          local.get $l2
          br_if 1 (;@2;)
          i32.const 1
          local.set $l2
          i32.const 0
          local.set $l3
          br 2 (;@1;)
        end
        local.get $l2
        br_if 0 (;@2;)
        local.get $p0
        i32.load
        local.tee $l2
        i32.load offset=4
        local.set $l3
        local.get $l2
        i32.load
        local.set $l2
        br 1 (;@1;)
      end
      local.get $l1
      i32.const -2147483648
      i32.store
      local.get $l1
      local.get $p0
      i32.store offset=12
      local.get $l1
      i32.const 4
      local.get $p0
      i32.load offset=28
      local.tee $p0
      i32.load8_u offset=28
      local.get $p0
      i32.load8_u offset=29
      call $_ZN3std9panicking20rust_panic_with_hook17h33fe77d38d305ca3E
      unreachable
    end
    local.get $l1
    local.get $l3
    i32.store offset=4
    local.get $l1
    local.get $l2
    i32.store
    local.get $l1
    i32.const 5
    local.get $p0
    i32.load offset=28
    local.tee $p0
    i32.load8_u offset=28
    local.get $p0
    i32.load8_u offset=29
    call $_ZN3std9panicking20rust_panic_with_hook17h33fe77d38d305ca3E
    unreachable)
  (func $_ZN3std9panicking20rust_panic_with_hook17h33fe77d38d305ca3E (type $t7) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32)
    (local $l4 i32) (local $l5 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l4
    global.set $__stack_pointer
    i32.const 0
    i32.const 0
    i32.load offset=1049888
    local.tee $l5
    i32.const 1
    i32.add
    i32.store offset=1049888
    block  ;; label = @1
      local.get $l5
      i32.const 0
      i32.lt_s
      br_if 0 (;@1;)
      block  ;; label = @2
        block  ;; label = @3
          i32.const 0
          i32.load8_u offset=1049896
          br_if 0 (;@3;)
          i32.const 0
          i32.const 0
          i32.load offset=1049892
          i32.const 1
          i32.add
          i32.store offset=1049892
          i32.const 0
          i32.load offset=1049884
          i32.const -1
          i32.gt_s
          br_if 1 (;@2;)
          br 2 (;@1;)
        end
        local.get $l4
        i32.const 8
        i32.add
        local.get $p0
        local.get $p1
        call_indirect $T0 (type $t3)
        unreachable
        unreachable
      end
      i32.const 0
      i32.const 0
      i32.store8 offset=1049896
      local.get $p2
      i32.eqz
      br_if 0 (;@1;)
      call $rust_panic
      unreachable
    end
    unreachable
    unreachable)
  (func $_ZN99_$LT$std..panicking..begin_panic_handler..StaticStrPayload$u20$as$u20$core..panic..PanicPayload$GT$6as_str17h35704e8c93457832E (type $t3) (param $p0 i32) (param $p1 i32)
    local.get $p0
    local.get $p1
    i64.load align=4
    i64.store)
  (func $_ZN17compiler_builtins3mem6memcpy17h4d1b3bf0b8e43c13E (type $t1) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
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
  (func $_ZN17compiler_builtins3mem6memset17h4739799fd37dc941E (type $t1) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    (local $l3 i32) (local $l4 i32) (local $l5 i32)
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
        loop  ;; label = @3
          local.get $l3
          local.get $p1
          i32.store8
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
      local.tee $l4
      i32.const -4
      i32.and
      local.tee $p2
      i32.add
      local.set $l3
      block  ;; label = @2
        local.get $p2
        i32.const 1
        i32.lt_s
        br_if 0 (;@2;)
        local.get $p1
        i32.const 255
        i32.and
        i32.const 16843009
        i32.mul
        local.set $p2
        loop  ;; label = @3
          local.get $l5
          local.get $p2
          i32.store
          local.get $l5
          i32.const 4
          i32.add
          local.tee $l5
          local.get $l3
          i32.lt_u
          br_if 0 (;@3;)
        end
      end
      local.get $l4
      i32.const 3
      i32.and
      local.set $p2
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
        i32.store8
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
  (func $memset (type $t1) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    local.get $p0
    local.get $p1
    local.get $p2
    call $_ZN17compiler_builtins3mem6memset17h4739799fd37dc941E)
  (func $memcpy (type $t1) (param $p0 i32) (param $p1 i32) (param $p2 i32) (result i32)
    local.get $p0
    local.get $p1
    local.get $p2
    call $_ZN17compiler_builtins3mem6memcpy17h4d1b3bf0b8e43c13E)
  (table $T0 10 10 funcref)
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1049897))
  (global $__heap_base i32 (i32.const 1049904))
  (export "memory" (memory $memory))
  (export "exec" (func $exec))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (elem $e0 (i32.const 1) func $_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u32$GT$3fmt17hd46d69ca3fa9eb1eE $_ZN42_$LT$$RF$T$u20$as$u20$core..fmt..Debug$GT$3fmt17hbd1c3de5eced27c6E $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17h9634f975d7713204E $_ZN4core5panic12PanicPayload6as_str17h59025c0ecbb0f54eE $_ZN99_$LT$std..panicking..begin_panic_handler..StaticStrPayload$u20$as$u20$core..panic..PanicPayload$GT$6as_str17h35704e8c93457832E $_ZN67_$LT$core..array..TryFromSliceError$u20$as$u20$core..fmt..Debug$GT$3fmt17h9039b1fe08508b23E $_ZN68_$LT$core..fmt..builders..PadAdapter$u20$as$u20$core..fmt..Write$GT$9write_str17hf46b591acfd1be0dE $_ZN68_$LT$core..fmt..builders..PadAdapter$u20$as$u20$core..fmt..Write$GT$10write_char17hdff090ddce8dafe2E $_ZN4core3fmt5Write9write_fmt17h07171b83fe780f81E)
  (data $.rodata (i32.const 1048576) "/Users/johannesspath/.cargo/registry/src/index.crates.io-6f17d22bba15001f/alloy-sol-types-0.6.3/src/types/data_type.rs/Users/johannesspath/.cargo/registry/src/index.crates.io-6f17d22bba15001f/soroban-sdk-21.6.0/src/bytes.rs\00v\00\10\00i\00\00\00>\02\00\00\0d\00\00\00\00\00\10\00v\00\00\00\ed\03\00\00\01\00\00\00/Users/johannesspath/.cargo/registry/src/index.crates.io-6f17d22bba15001f/alloy-sol-types-0.6.3/src/abi/decoder.rs\00\00\00\01\10\00r\00\00\00\ad\00\00\00\1b\00\00\00\00\01\10\00r\00\00\00\ba\00\00\00R\00\00\00\00\00\10\00v\00\00\00\a9\00\00\00\0d\00\00\00\00\00\10\00v\00\00\00\a9\00\00\00\13\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\06\00\00\00called `Result::unwrap()` on an `Err` valueTryFromSliceErrorsrc/lib.rs\00\00\00\02\10\00\0a\00\00\00#\00\00\00-\00\00\00capacity overflow\00\00\00\1c\02\10\00\11\00\00\00library/alloc/src/raw_vec.rs8\02\10\00\1c\00\00\00\19\00\00\00\05\00\00\00()attempt to add with overflow\00\00f\02\10\00\1c\00\00\00attempt to multiply with overflow\00\00\00\8c\02\10\00!\00\00\00)\00\00\00\01\00\00\00\00\00\00\00explicit panic\00\00\c4\02\10\00\0e\00\00\00: \00\00\01\00\00\00\00\00\00\00\dc\02\10\00\02\00\00\00\00\00\00\00\0c\00\00\00\04\00\00\00\07\00\00\00\08\00\00\00\09\00\00\00    ,\0a((\0a00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899 out of range for slice of length range end index \00\fb\03\10\00\10\00\00\00\d9\03\10\00\22\00\00\00source slice length () does not match destination slice length (\1c\04\10\00\15\00\00\001\04\10\00+\00\00\00\b8\02\10\00\01\00\00\00/Users/johannesspath/.cargo/registry/src/index.crates.io-6f17d22bba15001f/soroban-sdk-21.6.0/src/alloc.rs\00\00\00t\04\10\00i\00\00\00\1b\00\00\00\0a\00\00\00t\04\10\00i\00\00\00$\00\00\00\1b\00\00\00t\04\10\00i\00\00\00?\00\00\00\0d\00\00\00"))
