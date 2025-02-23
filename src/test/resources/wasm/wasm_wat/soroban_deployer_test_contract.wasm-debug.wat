(module $soroban_deployer_test_contract.wasm
  (type $t0 (func (param i64 i64 i64) (result i64)))
  (type $t1 (func (param i64 i64) (result i64)))
  (type $t2 (func (param i64) (result i64)))
  (type $t3 (func (result i64)))
  (type $t4 (func))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h524b30e8061fe9a1E (type $t0)))
  (import "l" "0" (func $_ZN17soroban_env_guest5guest6ledger17has_contract_data17h2c05f404b3fc0d68E (type $t1)))
  (import "l" "1" (func $_ZN17soroban_env_guest5guest6ledger17get_contract_data17hbaaedcf3f22a042cE (type $t1)))
  (func $init (type $t2) (param $p0 i64) (result i64)
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
    i64.const 256005548558
    local.get $p0
    i64.const -4294967292
    i64.and
    i64.const 2
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h524b30e8061fe9a1E
    drop
    i64.const 2)
  (func $value (type $t3) (result i64)
    (local $l0 i64)
    block  ;; label = @1
      block  ;; label = @2
        i64.const 256005548558
        i64.const 2
        call $_ZN17soroban_env_guest5guest6ledger17has_contract_data17h2c05f404b3fc0d68E
        i64.const 1
        i64.ne
        br_if 0 (;@2;)
        i64.const 256005548558
        i64.const 2
        call $_ZN17soroban_env_guest5guest6ledger17get_contract_data17hbaaedcf3f22a042cE
        local.tee $l0
        i64.const 255
        i64.and
        i64.const 4
        i64.eq
        br_if 1 (;@1;)
        unreachable
        unreachable
      end
      call $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E
      unreachable
    end
    local.get $l0
    i64.const -4294967292
    i64.and)
  (func $_ZN4core6option13unwrap_failed17h9aa82eb71128b127E (type $t4)
    call $_ZN4core9panicking5panic17hcaca2598a27ec0fcE
    unreachable)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t4)
    unreachable
    unreachable)
  (func $_ZN4core9panicking5panic17hcaca2598a27ec0fcE (type $t4)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ (type $t4))
  (memory $memory 16)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048576))
  (global $__heap_base i32 (i32.const 1048576))
  (export "memory" (memory $memory))
  (export "init" (func $init))
  (export "value" (func $value))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base)))
