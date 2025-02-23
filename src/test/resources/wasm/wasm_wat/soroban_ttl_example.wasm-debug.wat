(module $soroban_ttl_example.wasm
  (type $t0 (func (param i64 i64 i64 i64) (result i64)))
  (type $t1 (func (param i64 i64 i64) (result i64)))
  (type $t2 (func (param i64 i64) (result i64)))
  (type $t3 (func (param i64 i32 i32)))
  (type $t4 (func (result i64)))
  (type $t5 (func (param i32 i64)))
  (type $t6 (func))
  (import "l" "7" (func $_ZN17soroban_env_guest5guest6ledger24extend_contract_data_ttl17hfe78b0ca805be00cE (type $t0)))
  (import "l" "_" (func $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E (type $t1)))
  (import "b" "j" (func $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h65f4c5e4b5b0b386E (type $t2)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE (type $t2)))
  (import "l" "8" (func $_ZN17soroban_env_guest5guest6ledger45extend_current_contract_instance_and_code_ttl17hc38f5b2a5cae7be9E (type $t2)))
  (func $_ZN11soroban_sdk7storage7Storage10extend_ttl17h3b63d9467b8165b1E (type $t3) (param $p0 i64) (param $p1 i32) (param $p2 i32)
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h7c9f4f27229aa89fE
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
    call $_ZN17soroban_env_guest5guest6ledger24extend_contract_data_ttl17hfe78b0ca805be00cE
    drop)
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h7c9f4f27229aa89fE (type $t4) (result i64)
    (local $l0 i32) (local $l1 i64) (local $l2 i32) (local $l3 i32) (local $l4 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l0
    global.set $__stack_pointer
    i64.const 0
    local.set $l1
    i32.const -5
    local.set $l2
    block  ;; label = @1
      block  ;; label = @2
        block  ;; label = @3
          loop  ;; label = @4
            local.get $l2
            i32.eqz
            br_if 1 (;@3;)
            i32.const 1
            local.set $l3
            block  ;; label = @5
              local.get $l2
              i32.const 1048581
              i32.add
              i32.load8_u
              local.tee $l4
              i32.const 95
              i32.eq
              br_if 0 (;@5;)
              block  ;; label = @6
                local.get $l4
                i32.const -48
                i32.add
                i32.const 255
                i32.and
                i32.const 10
                i32.lt_u
                br_if 0 (;@6;)
                block  ;; label = @7
                  local.get $l4
                  i32.const -65
                  i32.add
                  i32.const 255
                  i32.and
                  i32.const 26
                  i32.lt_u
                  br_if 0 (;@7;)
                  local.get $l4
                  i32.const -97
                  i32.add
                  i32.const 255
                  i32.and
                  i32.const 25
                  i32.gt_u
                  br_if 5 (;@2;)
                  local.get $l4
                  i32.const -59
                  i32.add
                  local.set $l3
                  br 2 (;@5;)
                end
                local.get $l4
                i32.const -53
                i32.add
                local.set $l3
                br 1 (;@5;)
              end
              local.get $l4
              i32.const -46
              i32.add
              local.set $l3
            end
            local.get $l1
            i64.const 6
            i64.shl
            local.get $l3
            i64.extend_i32_u
            i64.const 255
            i64.and
            i64.or
            local.set $l1
            local.get $l2
            i32.const 1
            i32.add
            local.set $l2
            br 0 (;@4;)
          end
        end
        local.get $l1
        i64.const 8
        i64.shl
        i64.const 14
        i64.or
        local.set $l1
        br 1 (;@1;)
      end
      i32.const 1048576
      i64.extend_i32_u
      i64.const 32
      i64.shl
      i64.const 4
      i64.or
      i64.const 21474836484
      call $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h65f4c5e4b5b0b386E
      local.set $l1
    end
    local.get $l0
    local.get $l1
    i64.store offset=8
    local.get $l0
    i32.const 8
    i32.add
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 4
    i64.or
    i64.const 4294967300
    call $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h5a03b2d65ac335eeE
    local.set $l1
    local.get $l0
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get $l1)
  (func $_ZN11soroban_sdk7storage7Storage3set17h3d48e79aeabe12caE (type $t5) (param $p0 i32) (param $p1 i64)
    call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17h7c9f4f27229aa89fE
    local.get $p0
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 5
    i64.or
    local.get $p1
    call $_ZN17soroban_env_guest5guest6ledger17put_contract_data17h0b78091c07fde9a3E
    drop)
  (func $setup (type $t4) (result i64)
    i32.const 0
    i64.const 1
    call $_ZN11soroban_sdk7storage7Storage3set17h3d48e79aeabe12caE
    i32.const 1
    i64.const 2
    call $_ZN11soroban_sdk7storage7Storage3set17h3d48e79aeabe12caE
    i32.const 2
    i64.const 0
    call $_ZN11soroban_sdk7storage7Storage3set17h3d48e79aeabe12caE
    i64.const 2)
  (func $extend_persistent (type $t4) (result i64)
    i64.const 1
    i32.const 1000
    i32.const 5000
    call $_ZN11soroban_sdk7storage7Storage10extend_ttl17h3b63d9467b8165b1E
    i64.const 2)
  (func $extend_instance (type $t4) (result i64)
    i64.const 8589934592004
    i64.const 42949672960004
    call $_ZN17soroban_env_guest5guest6ledger45extend_current_contract_instance_and_code_ttl17hc38f5b2a5cae7be9E
    drop
    i64.const 2)
  (func $extend_temporary (type $t4) (result i64)
    i64.const 0
    i32.const 3000
    i32.const 7000
    call $_ZN11soroban_sdk7storage7Storage10extend_ttl17h3b63d9467b8165b1E
    i64.const 2)
  (func $_ (type $t6))
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048581))
  (global $__heap_base i32 (i32.const 1048592))
  (export "memory" (memory $memory))
  (export "setup" (func $setup))
  (export "extend_persistent" (func $extend_persistent))
  (export "extend_instance" (func $extend_instance))
  (export "extend_temporary" (func $extend_temporary))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (data $.rodata (i32.const 1048576) "MyKey"))
