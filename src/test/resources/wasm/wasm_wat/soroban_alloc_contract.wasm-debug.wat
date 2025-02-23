(module $soroban_alloc_contract.wasm
  (type $t0 (func (param i32 i32 i32) (result i32)))
  (type $t1 (func (param i32 i32) (result i32)))
  (type $t2 (func (param i32 i32)))
  (type $t3 (func (param i32 i32 i32)))
  (type $t4 (func (param i32 i32 i32 i32)))
  (type $t5 (func (param i32 i32 i32 i32) (result i32)))
  (type $t6 (func (param i32)))
  (type $t7 (func (param i64) (result i64)))
  (type $t8 (func))
  (func $_ZN5alloc5alloc6Global10alloc_impl17h937169c39eac7921E (type $t3) (param $p0 i32) (param $p1 i32) (param $p2 i32)
    block  ;; label = @1
      local.get $p2
      i32.eqz
      br_if 0 (;@1;)
      i32.const 0
      i32.load8_u offset=1048952
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
  (func $__rust_alloc (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32) (local $l3 i32)
    call $_ZN11soroban_sdk5alloc16BumpPointerLocal10maybe_init17h4c255a6d0fd8ed49E
    block  ;; label = @1
      local.get $p1
      i32.const 0
      i32.load offset=1048944
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
        i32.load offset=1048948
        i32.le_u
        br_if 0 (;@2;)
        local.get $p0
        local.get $p1
        call $_ZN11soroban_sdk5alloc16BumpPointerLocal10alloc_slow17hc44aa66f90e911c4E
        return
      end
      i32.const 0
      local.get $l3
      i32.store offset=1048944
      local.get $l2
      return
    end
    i32.const 1048896
    call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
    unreachable)
  (func $_ZN5alloc7raw_vec11finish_grow17habd59b7615cffebfE (type $t4) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32)
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
            call $_ZN5alloc5alloc6Global10alloc_impl17h937169c39eac7921E
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
        call $_ZN5alloc5alloc6Global10alloc_impl17h937169c39eac7921E
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
  (func $__rust_realloc (type $t5) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (result i32)
    (local $l4 i32) (local $l5 i32)
    call $_ZN11soroban_sdk5alloc16BumpPointerLocal10maybe_init17h4c255a6d0fd8ed49E
    block  ;; label = @1
      local.get $p2
      i32.const 0
      i32.load offset=1048944
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
          i32.load offset=1048948
          i32.le_u
          br_if 0 (;@3;)
          local.get $p3
          local.get $p2
          call $_ZN11soroban_sdk5alloc16BumpPointerLocal10alloc_slow17hc44aa66f90e911c4E
          local.set $l4
          br 1 (;@2;)
        end
        i32.const 0
        local.get $l5
        i32.store offset=1048944
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
    i32.const 1048896
    call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
    unreachable)
  (func $_ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$8grow_one17h7c3ddcb577ab5c66E (type $t6) (param $p0 i32)
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
        i32.const 0
        local.set $l3
        local.get $l2
        i32.const 1
        i32.shl
        local.get $l2
        i32.const 1
        i32.add
        local.get $l2
        i32.const 0
        i32.gt_s
        select
        local.tee $l4
        i32.const 4
        local.get $l4
        i32.const 4
        i32.gt_u
        select
        local.tee $l5
        i32.const 2
        i32.shl
        local.set $l6
        local.get $l4
        i32.const 536870912
        i32.lt_u
        i32.const 2
        i32.shl
        local.set $l4
        block  ;; label = @3
          local.get $l2
          i32.eqz
          br_if 0 (;@3;)
          local.get $l1
          local.get $l2
          i32.const 2
          i32.shl
          i32.store offset=28
          local.get $l1
          local.get $p0
          i32.load offset=4
          i32.store offset=20
          i32.const 4
          local.set $l3
        end
        local.get $l1
        local.get $l3
        i32.store offset=24
        local.get $l1
        i32.const 8
        i32.add
        local.get $l4
        local.get $l6
        local.get $l1
        i32.const 20
        i32.add
        call $_ZN5alloc7raw_vec11finish_grow17habd59b7615cffebfE
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
    local.get $l5
    i32.store
    local.get $p0
    local.get $l2
    i32.store offset=4
    local.get $l1
    i32.const 32
    i32.add
    global.set $__stack_pointer)
  (func $_ZN5alloc7raw_vec12handle_error17h76131d670f53a5eeE (type $t2) (param $p0 i32) (param $p1 i32)
    block  ;; label = @1
      local.get $p0
      br_if 0 (;@1;)
      call $_ZN5alloc7raw_vec17capacity_overflow17h76f9308d7d8b5961E
      unreachable
    end
    unreachable
    unreachable)
  (func $sum (type $t7) (param $p0 i64) (result i64)
    (local $l1 i32) (local $l2 i32) (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
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
        local.set $l2
        i32.const 0
        local.set $l3
        local.get $l1
        i32.const 0
        i32.store offset=12
        local.get $l1
        i64.const 17179869184
        i64.store offset=4 align=4
        i32.const 1
        local.set $l4
        i32.const 4
        local.set $l5
        i32.const 0
        local.set $l6
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l6
            local.get $l2
            i32.ge_u
            br_if 1 (;@3;)
            block  ;; label = @5
              local.get $l4
              i32.const -1
              i32.add
              local.get $l1
              i32.load offset=4
              i32.ne
              br_if 0 (;@5;)
              local.get $l1
              i32.const 4
              i32.add
              call $_ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$8grow_one17h7c3ddcb577ab5c66E
              local.get $l1
              i32.load offset=8
              local.set $l5
            end
            local.get $l5
            local.get $l3
            i32.add
            local.get $l6
            i32.store
            local.get $l3
            i32.const 4
            i32.add
            local.set $l3
            local.get $l1
            local.get $l4
            i32.store offset=12
            local.get $l4
            i32.const 1
            i32.add
            local.set $l4
            local.get $l6
            local.get $l6
            local.get $l2
            i32.lt_u
            i32.add
            local.set $l6
            br 0 (;@4;)
          end
        end
        i32.const 0
        local.set $l6
        loop  ;; label = @3
          local.get $l3
          i32.eqz
          br_if 2 (;@1;)
          block  ;; label = @4
            local.get $l6
            local.get $l5
            i32.load
            i32.add
            local.tee $l4
            local.get $l6
            i32.lt_u
            br_if 0 (;@4;)
            local.get $l3
            i32.const -4
            i32.add
            local.set $l3
            local.get $l5
            i32.const 4
            i32.add
            local.set $l5
            local.get $l4
            local.set $l6
            br 1 (;@3;)
          end
        end
        i32.const 1048588
        call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
        unreachable
      end
      unreachable
      unreachable
    end
    local.get $l1
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l6
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or)
  (func $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E (type $t6) (param $p0 i32)
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
    i32.const 1048704
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
  (func $_ZN5alloc7raw_vec17capacity_overflow17h76f9308d7d8b5961E (type $t8)
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
    i32.const 1048624
    i32.store offset=8
    local.get $l0
    i64.const 4
    i64.store offset=16 align=4
    local.get $l0
    i32.const 8
    i32.add
    i32.const 1048660
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t2) (param $p0 i32) (param $p1 i32)
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
  (func $rust_begin_unwind (type $t6) (param $p0 i32)
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
  (func $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17h9634f975d7713204E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
    (local $l2 i32) (local $l3 i32) (local $l4 i32) (local $l5 i32) (local $l6 i32) (local $l7 i32) (local $l8 i32) (local $l9 i32) (local $l10 i32) (local $l11 i32) (local $l12 i32) (local $l13 i32)
    local.get $p0
    i32.load offset=4
    local.set $l2
    local.get $p0
    i32.load
    local.set $l3
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          local.get $p1
          i32.load
          local.tee $l4
          local.get $p1
          i32.load offset=8
          local.tee $p0
          i32.or
          i32.eqz
          br_if 0 (;@3;)
          block  ;; label = @4
            local.get $p0
            i32.eqz
            br_if 0 (;@4;)
            local.get $l3
            local.get $l2
            i32.add
            local.set $l5
            block  ;; label = @5
              block  ;; label = @6
                local.get $p1
                i32.load offset=12
                local.tee $l6
                br_if 0 (;@6;)
                i32.const 0
                local.set $l7
                local.get $l3
                local.set $l8
                br 1 (;@5;)
              end
              i32.const 0
              local.set $l7
              i32.const 0
              local.set $l9
              local.get $l3
              local.set $l8
              loop  ;; label = @6
                local.get $l8
                local.tee $p0
                local.get $l5
                i32.eq
                br_if 2 (;@4;)
                block  ;; label = @7
                  block  ;; label = @8
                    local.get $p0
                    i32.load8_s
                    local.tee $l8
                    i32.const -1
                    i32.le_s
                    br_if 0 (;@8;)
                    local.get $p0
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
                    local.get $p0
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
                    local.get $p0
                    i32.const 3
                    i32.add
                    local.set $l8
                    br 1 (;@7;)
                  end
                  local.get $p0
                  i32.const 4
                  i32.add
                  local.set $l8
                end
                local.get $l8
                local.get $p0
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
              local.tee $p0
              i32.const -1
              i32.gt_s
              br_if 0 (;@5;)
              local.get $p0
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
                  local.get $l2
                  i32.ge_u
                  br_if 0 (;@7;)
                  i32.const 0
                  local.set $p0
                  local.get $l3
                  local.get $l7
                  i32.add
                  i32.load8_s
                  i32.const -65
                  i32.gt_s
                  br_if 1 (;@6;)
                  br 2 (;@5;)
                end
                i32.const 0
                local.set $p0
                local.get $l7
                local.get $l2
                i32.ne
                br_if 1 (;@5;)
              end
              local.get $l3
              local.set $p0
            end
            local.get $l7
            local.get $l2
            local.get $p0
            select
            local.set $l2
            local.get $p0
            local.get $l3
            local.get $p0
            select
            local.set $l3
          end
          block  ;; label = @4
            local.get $l4
            br_if 0 (;@4;)
            local.get $p1
            i32.load offset=20
            local.get $l3
            local.get $l2
            local.get $p1
            i32.load offset=24
            i32.load offset=12
            call_indirect $T0 (type $t0)
            return
          end
          local.get $p1
          i32.load offset=4
          local.set $l10
          block  ;; label = @4
            local.get $l2
            i32.const 16
            i32.lt_u
            br_if 0 (;@4;)
            local.get $l2
            local.get $l3
            local.get $l3
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
            local.set $l4
            i32.const 0
            local.set $l6
            i32.const 0
            local.set $p0
            block  ;; label = @5
              local.get $l3
              local.get $l7
              i32.eq
              br_if 0 (;@5;)
              i32.const 0
              local.set $p0
              block  ;; label = @6
                local.get $l9
                i32.const -4
                i32.gt_u
                br_if 0 (;@6;)
                i32.const 0
                local.set $p0
                i32.const 0
                local.set $l5
                loop  ;; label = @7
                  local.get $p0
                  local.get $l3
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
                  local.set $p0
                  local.get $l5
                  i32.const 4
                  i32.add
                  local.tee $l5
                  br_if 0 (;@7;)
                end
              end
              local.get $l3
              local.set $l8
              loop  ;; label = @6
                local.get $p0
                local.get $l8
                i32.load8_s
                i32.const -65
                i32.gt_s
                i32.add
                local.set $p0
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
              local.get $l4
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
              local.get $l4
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
              local.get $l4
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
            local.get $p0
            i32.add
            local.set $l6
            loop  ;; label = @5
              local.get $l7
              local.set $l4
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
                local.get $l4
                local.get $l13
                i32.const 1008
                i32.and
                i32.add
                local.set $l9
                i32.const 0
                local.set $l8
                local.get $l4
                local.set $p0
                loop  ;; label = @7
                  local.get $p0
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
                  local.get $p0
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
                  local.get $p0
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
                  local.get $p0
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
                  local.get $p0
                  i32.const 16
                  i32.add
                  local.tee $p0
                  local.get $l9
                  i32.ne
                  br_if 0 (;@7;)
                end
              end
              local.get $l5
              local.get $l11
              i32.sub
              local.set $l5
              local.get $l4
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
            local.get $l4
            local.get $l11
            i32.const 252
            i32.and
            i32.const 2
            i32.shl
            i32.add
            local.tee $l8
            i32.load
            local.tee $p0
            i32.const -1
            i32.xor
            i32.const 7
            i32.shr_u
            local.get $p0
            i32.const 6
            i32.shr_u
            i32.or
            i32.const 16843009
            i32.and
            local.set $p0
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
            local.get $p0
            i32.add
            local.set $p0
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
            local.get $p0
            i32.add
            local.set $p0
            br 2 (;@2;)
          end
          block  ;; label = @4
            local.get $l2
            br_if 0 (;@4;)
            i32.const 0
            local.set $l6
            br 3 (;@1;)
          end
          local.get $l2
          i32.const 3
          i32.and
          local.set $l8
          block  ;; label = @4
            block  ;; label = @5
              local.get $l2
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
            local.get $l3
            local.set $p0
            local.get $l2
            i32.const 12
            i32.and
            local.tee $l9
            local.set $l7
            loop  ;; label = @5
              local.get $l6
              local.get $p0
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.get $p0
              i32.const 1
              i32.add
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.get $p0
              i32.const 2
              i32.add
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.get $p0
              i32.const 3
              i32.add
              i32.load8_s
              i32.const -65
              i32.gt_s
              i32.add
              local.set $l6
              local.get $p0
              i32.const 4
              i32.add
              local.set $p0
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
          local.get $l3
          local.get $l9
          i32.add
          local.set $p0
          loop  ;; label = @4
            local.get $l6
            local.get $p0
            i32.load8_s
            i32.const -65
            i32.gt_s
            i32.add
            local.set $l6
            local.get $p0
            i32.const 1
            i32.add
            local.set $p0
            local.get $l8
            i32.const -1
            i32.add
            local.tee $l8
            br_if 0 (;@4;)
            br 3 (;@1;)
          end
        end
        local.get $p1
        i32.load offset=20
        local.get $l3
        local.get $l2
        local.get $p1
        i32.load offset=24
        i32.load offset=12
        call_indirect $T0 (type $t0)
        return
      end
      local.get $p0
      i32.const 8
      i32.shr_u
      i32.const 459007
      i32.and
      local.get $p0
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
        local.set $p0
        block  ;; label = @3
          block  ;; label = @4
            block  ;; label = @5
              local.get $p1
              i32.load8_u offset=32
              br_table 2 (;@3;) 0 (;@5;) 1 (;@4;) 2 (;@3;) 2 (;@3;)
            end
            local.get $l5
            local.set $p0
            i32.const 0
            local.set $l5
            br 1 (;@3;)
          end
          local.get $l5
          i32.const 1
          i32.shr_u
          local.set $p0
          local.get $l5
          i32.const 1
          i32.add
          i32.const 1
          i32.shr_u
          local.set $l5
        end
        local.get $p0
        i32.const 1
        i32.add
        local.set $p0
        local.get $p1
        i32.load offset=16
        local.set $l9
        local.get $p1
        i32.load offset=24
        local.set $l8
        local.get $p1
        i32.load offset=20
        local.set $l7
        loop  ;; label = @3
          local.get $p0
          i32.const -1
          i32.add
          local.tee $p0
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
      local.get $p1
      i32.load offset=20
      local.get $l3
      local.get $l2
      local.get $p1
      i32.load offset=24
      i32.load offset=12
      call_indirect $T0 (type $t0)
      return
    end
    i32.const 1
    local.set $p0
    block  ;; label = @1
      local.get $l7
      local.get $l3
      local.get $l2
      local.get $l8
      i32.load offset=12
      call_indirect $T0 (type $t0)
      br_if 0 (;@1;)
      i32.const 0
      local.set $p0
      block  ;; label = @2
        loop  ;; label = @3
          block  ;; label = @4
            local.get $l5
            local.get $p0
            i32.ne
            br_if 0 (;@4;)
            local.get $l5
            local.set $p0
            br 2 (;@2;)
          end
          local.get $p0
          i32.const 1
          i32.add
          local.set $p0
          local.get $l7
          local.get $l9
          local.get $l8
          i32.load offset=16
          call_indirect $T0 (type $t1)
          i32.eqz
          br_if 0 (;@3;)
        end
        local.get $p0
        i32.const -1
        i32.add
        local.set $p0
      end
      local.get $p0
      local.get $l5
      i32.lt_u
      local.set $p0
    end
    local.get $p0)
  (func $_ZN4core9panicking14panic_explicit17h0d32b058017db662E (type $t8)
    (local $l0 i32)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    local.get $l0
    i32.const 1
    i32.store offset=4
    local.get $l0
    i32.const 1048756
    i32.store
    local.get $l0
    i64.const 1
    i64.store offset=12 align=4
    local.get $l0
    i32.const 1
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i32.const 1048780
    i64.extend_i32_u
    i64.or
    i64.store offset=24
    local.get $l0
    local.get $l0
    i32.const 24
    i32.add
    i32.store offset=8
    local.get $l0
    i32.const 1048928
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core9panicking11panic_const24panic_const_mul_overflow17hfc625200574f06ecE (type $t8)
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
    i32.const 1048748
    i32.store offset=8
    local.get $l0
    i64.const 4
    i64.store offset=16 align=4
    local.get $l0
    i32.const 8
    i32.add
    i32.const 1048912
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN11soroban_sdk5alloc16BumpPointerLocal10maybe_init17h4c255a6d0fd8ed49E (type $t8)
    (local $l0 i32)
    block  ;; label = @1
      block  ;; label = @2
        i32.const 0
        i32.load offset=1048948
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
        i32.store offset=1048948
        i32.const 0
        local.get $l0
        i32.store offset=1048944
      end
      return
    end
    call $_ZN4core9panicking11panic_const24panic_const_mul_overflow17hfc625200574f06ecE
    unreachable)
  (func $_ZN11soroban_sdk5alloc16BumpPointerLocal10alloc_slow17hc44aa66f90e911c4E (type $t1) (param $p0 i32) (param $p1 i32) (result i32)
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
          i32.load offset=1048948
          local.get $l4
          i32.add
          i32.store offset=1048948
          call $_ZN11soroban_sdk5alloc16BumpPointerLocal10maybe_init17h4c255a6d0fd8ed49E
          i32.const 0
          i32.load offset=1048944
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
          i32.load offset=1048948
          i32.gt_u
          br_if 0 (;@3;)
        end
        i32.const 0
        local.get $l6
        i32.store offset=1048944
        local.get $p1
        return
      end
      call $_ZN11soroban_sdk5alloc16BumpPointerLocal17alloc_slow_inline19panic_cold_explicit17h726df9e1c11adc19E
      unreachable
    end
    i32.const 1048896
    call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
    unreachable)
  (func $_ZN11soroban_sdk5alloc16BumpPointerLocal17alloc_slow_inline19panic_cold_explicit17h726df9e1c11adc19E (type $t8)
    call $_ZN4core9panicking14panic_explicit17h0d32b058017db662E
    unreachable)
  (func $_ (type $t8))
  (func $rust_panic (type $t8)
    unreachable
    unreachable)
  (func $_ZN4core5panic12PanicPayload6as_str17h59025c0ecbb0f54eE (type $t2) (param $p0 i32) (param $p1 i32)
    local.get $p0
    i32.const 0
    i32.store)
  (func $_ZN3std3sys9backtrace26__rust_end_short_backtrace17h2bcfc60c3cf0a312E (type $t6) (param $p0 i32)
    local.get $p0
    call $_ZN3std9panicking19begin_panic_handler28_$u7b$$u7b$closure$u7d$$u7d$17h98de848d678bad07E
    unreachable)
  (func $_ZN3std9panicking19begin_panic_handler28_$u7b$$u7b$closure$u7d$$u7d$17h98de848d678bad07E (type $t6) (param $p0 i32)
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
      i32.const 2
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
    i32.const 3
    local.get $p0
    i32.load offset=28
    local.tee $p0
    i32.load8_u offset=28
    local.get $p0
    i32.load8_u offset=29
    call $_ZN3std9panicking20rust_panic_with_hook17h33fe77d38d305ca3E
    unreachable)
  (func $_ZN3std9panicking20rust_panic_with_hook17h33fe77d38d305ca3E (type $t4) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32)
    (local $l4 i32) (local $l5 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l4
    global.set $__stack_pointer
    i32.const 0
    i32.const 0
    i32.load offset=1048960
    local.tee $l5
    i32.const 1
    i32.add
    i32.store offset=1048960
    block  ;; label = @1
      local.get $l5
      i32.const 0
      i32.lt_s
      br_if 0 (;@1;)
      block  ;; label = @2
        block  ;; label = @3
          i32.const 0
          i32.load8_u offset=1048968
          br_if 0 (;@3;)
          i32.const 0
          i32.const 0
          i32.load offset=1048964
          i32.const 1
          i32.add
          i32.store offset=1048964
          i32.const 0
          i32.load offset=1048956
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
        call_indirect $T0 (type $t2)
        unreachable
        unreachable
      end
      i32.const 0
      i32.const 0
      i32.store8 offset=1048968
      local.get $p2
      i32.eqz
      br_if 0 (;@1;)
      call $rust_panic
      unreachable
    end
    unreachable
    unreachable)
  (func $_ZN99_$LT$std..panicking..begin_panic_handler..StaticStrPayload$u20$as$u20$core..panic..PanicPayload$GT$6as_str17h35704e8c93457832E (type $t2) (param $p0 i32) (param $p1 i32)
    local.get $p0
    local.get $p1
    i64.load align=4
    i64.store)
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
  (table $T0 4 4 funcref)
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048969))
  (global $__heap_base i32 (i32.const 1048976))
  (export "memory" (memory $memory))
  (export "sum" (func $sum))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (elem $e0 (i32.const 1) func $_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17h9634f975d7713204E $_ZN4core5panic12PanicPayload6as_str17h59025c0ecbb0f54eE $_ZN99_$LT$std..panicking..begin_panic_handler..StaticStrPayload$u20$as$u20$core..panic..PanicPayload$GT$6as_str17h35704e8c93457832E)
  (data $.rodata (i32.const 1048576) "src/lib.rs\00\00\00\00\10\00\0a\00\00\00\12\00\00\00\0d\00\00\00capacity overflow\00\00\00\1c\00\10\00\11\00\00\00library/alloc/src/raw_vec.rs8\00\10\00\1c\00\00\00\19\00\00\00\05\00\00\00attempt to add with overflowd\00\10\00\1c\00\00\00attempt to multiply with overflow\00\00\00\88\00\10\00!\00\00\00\01\00\00\00\00\00\00\00explicit panic\00\00\bc\00\10\00\0e\00\00\00/Users/johannesspath/.cargo/registry/src/index.crates.io-6f17d22bba15001f/soroban-sdk-21.6.0/src/alloc.rs\00\00\00\d4\00\10\00i\00\00\00\1b\00\00\00\0a\00\00\00\d4\00\10\00i\00\00\00$\00\00\00\1b\00\00\00\d4\00\10\00i\00\00\00?\00\00\00\0d\00\00\00"))
