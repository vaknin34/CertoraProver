(module $soroban_increment_contract.wasm
  (type $t0 (func (param i32)))
  (type $t1 (func (param i64 i64) (result i64)))
  (type $t2 (func (param i64 i64 i64) (result i64)))
  (type $t3 (func (result i64)))
  (type $t4 (func (result i32)))
  (type $t5 (func))
  (import "env" "CVT_assert_c" (func $CVT_assert_c (type $t0)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17h8f0a468dcf349270E (type $t1)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h15229b227a0fbb18E (type $t1)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h7a71a58211494b3aE (type $t2)))
  (import "l" "8" (func $_ZN17soroban_env_guest5guest6ledger45extend_current_contract_instance_and_code_ttl17h308a084899e50197E (type $t1)))
  (func $_ZN26soroban_increment_contract10CVT_assert17hf712d4ffa31fe71eE (type $t0) (param $p0 i32)
    local.get $p0
    call $CVT_assert_c)
  (func $increment (type $t3) (result i64)
    call $_ZN26soroban_increment_contract17IncrementContract9increment17h630de0feb0326bf5E
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or)
  (func $_ZN26soroban_increment_contract17IncrementContract9increment17h630de0feb0326bf5E (type $t4) (result i32)
    (local $l0 i32) (local $l1 i64)
    i32.const 0
    local.set $l0
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          i64.const 253576579652878
          i64.const 2
          call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17h8f0a468dcf349270E
          i64.const 1
          i64.ne
          br_if 0 (;@3;)
          i64.const 253576579652878
          i64.const 2
          call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17h15229b227a0fbb18E
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
        br_if 1 (;@1;)
        call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
        unreachable
      end
      unreachable
      unreachable
    end
    i64.const 253576579652878
    local.get $l0
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h7a71a58211494b3aE
    drop
    i64.const 214748364804
    i64.const 429496729604
    call $_ZN17soroban_env_guest5guest6ledger45extend_current_contract_instance_and_code_ttl17h308a084899e50197E
    drop
    local.get $l0)
  (func $verify_increment_gt_one (type $t3) (result i64)
    call $_ZN26soroban_increment_contract17IncrementContract9increment17h630de0feb0326bf5E
    i32.const 1
    i32.gt_u
    call $_ZN26soroban_increment_contract10CVT_assert17hf712d4ffa31fe71eE
    i64.const 2)
  (func $verify_increment_geq_one (type $t3) (result i64)
    call $_ZN26soroban_increment_contract17IncrementContract9increment17h630de0feb0326bf5E
    i32.const 0
    i32.ne
    call $_ZN26soroban_increment_contract10CVT_assert17hf712d4ffa31fe71eE
    i64.const 2)
  (func $verify_increment (type $t3) (result i64)
    (local $l0 i32) (local $l1 i32)
    call $_ZN26soroban_increment_contract17IncrementContract9increment17h630de0feb0326bf5E
    local.set $l0
    call $_ZN26soroban_increment_contract17IncrementContract9increment17h630de0feb0326bf5E
    local.set $l1
    block  ;; label = @1
      local.get $l0
      i32.const 1
      i32.add
      local.tee $l0
      br_if 0 (;@1;)
      call $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E
      unreachable
    end
    local.get $l1
    local.get $l0
    i32.eq
    call $_ZN26soroban_increment_contract10CVT_assert17hf712d4ffa31fe71eE
    i64.const 2)
  (func $_ZN4core9panicking11panic_const24panic_const_add_overflow17hfbb0d1b9e0cc3274E (type $t5)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $verify_increment_2 (type $t3) (result i64)
    call $_ZN26soroban_increment_contract17IncrementContract9increment17h630de0feb0326bf5E
    call $_ZN26soroban_increment_contract17IncrementContract9increment17h630de0feb0326bf5E
    i32.le_u
    call $_ZN26soroban_increment_contract10CVT_assert17hf712d4ffa31fe71eE
    i64.const 2)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t5)
    unreachable
    unreachable)
  (func $_ (type $t5))
  (memory $memory 16)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048576))
  (global $__heap_base i32 (i32.const 1048576))
  (export "memory" (memory $memory))
  (export "increment" (func $increment))
  (export "verify_increment_gt_one" (func $verify_increment_gt_one))
  (export "verify_increment_geq_one" (func $verify_increment_geq_one))
  (export "verify_increment" (func $verify_increment))
  (export "verify_increment_2" (func $verify_increment_2))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base)))
