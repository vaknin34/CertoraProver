(module $soroban_errors_contract.wasm
  (type $t0 (func (param i64 i64) (result i64)))
  (type $t1 (func (param i64 i64 i64) (result i64)))
  (type $t2 (func (result i64)))
  (type $t3 (func))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17hd2a7405285beb92bE (type $t0)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h716dbb60a8fc9019E (type $t0)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E (type $t1)))
  (func $increment (type $t2) (result i64)
    (local $l0 i32) (local $l1 i64)
    i32.const 0
    local.set $l0
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
          local.tee $l1
          i64.const 255
          i64.and
          i64.const 4
          i64.ne
          br_if 1 (;@2;)
          local.get $l1
          i64.const 32
          i64.shr_u
          i32.wrap_i64
          local.set $l0
        end
        local.get $l0
        i32.const 1
        i32.add
        local.tee $l0
        i32.eqz
        br_if 1 (;@1;)
        i64.const 4294967299
        local.set $l1
        block  ;; label = @3
          local.get $l0
          i32.const 6
          i32.ge_u
          br_if 0 (;@3;)
          i64.const 253576579652878
          local.get $l0
          i64.extend_i32_u
          i64.const 32
          i64.shl
          i64.const 4
          i64.or
          local.tee $l1
          i64.const 2
          call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E
          drop
        end
        local.get $l1
        return
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
