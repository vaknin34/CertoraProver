(module $soroban_events_contract.wasm
  (type $t0 (func (param i64 i64) (result i64)))
  (type $t1 (func (param i64 i64 i64) (result i64)))
  (type $t2 (func (result i64)))
  (type $t3 (func))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE (type $t0)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E (type $t0)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E (type $t1)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE (type $t0)))
  (import "x" "1" (func $_ZN17soroban_env_guest5guest7context14contract_event17h9ea3fb3010f39aa8E (type $t0)))
  (func $increment (type $t2) (result i64)
    (local $l0 i32) (local $l1 i32) (local $l2 i64)
    global.get $__stack_pointer
    i32.const 32
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    i32.const 0
    local.set $l1
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          i64.const 253576579652878
          i64.const 2
          call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE
          i64.const 1
          i64.ne
          br_if 0 (;@3;)
          i64.const 253576579652878
          i64.const 2
          call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E
          local.tee $l2
          i64.const 255
          i64.and
          i64.const 4
          i64.ne
          br_if 1 (;@2;)
          local.get $l2
          i64.const 32
          i64.shr_u
          i32.wrap_i64
          local.set $l1
        end
        local.get $l1
        i32.const 1
        i32.add
        local.tee $l1
        i32.eqz
        br_if 1 (;@1;)
        i64.const 253576579652878
        local.get $l1
        i64.extend_i32_u
        i64.const 32
        i64.shl
        i64.const 4
        i64.or
        local.tee $l2
        i64.const 2
        call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E
        drop
        local.get $l0
        i64.const 3372789210509277454
        i64.store offset=8
        local.get $l0
        i64.const 253576579652878
        i64.store
        i32.const 0
        local.set $l1
        loop  ;; label = @3
          block  ;; label = @4
            local.get $l1
            i32.const 16
            i32.ne
            br_if 0 (;@4;)
            i32.const 0
            local.set $l1
            block  ;; label = @5
              loop  ;; label = @6
                local.get $l1
                i32.const 16
                i32.eq
                br_if 1 (;@5;)
                local.get $l0
                i32.const 16
                i32.add
                local.get $l1
                i32.add
                local.get $l0
                local.get $l1
                i32.add
                i64.load
                i64.store
                local.get $l1
                i32.const 8
                i32.add
                local.set $l1
                br 0 (;@6;)
              end
            end
            local.get $l0
            i32.const 16
            i32.add
            i64.extend_i32_u
            i64.const 32
            i64.shl
            i64.const 4
            i64.or
            i64.const 8589934596
            call $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE
            local.get $l2
            call $_ZN17soroban_env_guest5guest7context14contract_event17h9ea3fb3010f39aa8E
            drop
            local.get $l0
            i32.const 32
            i32.add
            global.set $__stack_pointer
            local.get $l2
            return
          end
          local.get $l0
          i32.const 16
          i32.add
          local.get $l1
          i32.add
          i64.const 2
          i64.store
          local.get $l1
          i32.const 8
          i32.add
          local.set $l1
          br 0 (;@3;)
        end
      end
      unreachable
      unreachable
    end
    call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
    unreachable)
  (func $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E (type $t3)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t3)
    unreachable
    unreachable)
  (func $_ (type $t3))
  (memory $memory 16)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048576))
  (global $__heap_base i32 (i32.const 1048576))
  (export "memory" (memory $memory))
  (export "increment" (func $increment))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base)))
