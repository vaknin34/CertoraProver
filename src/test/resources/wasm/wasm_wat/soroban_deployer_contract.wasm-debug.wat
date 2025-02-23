(module $soroban_deployer_contract.wasm
  (type $t0 (func (result i64)))
  (type $t1 (func (param i64) (result i64)))
  (type $t2 (func (param i64 i64 i64) (result i64)))
  (type $t3 (func (param i64 i64) (result i64)))
  (type $t4 (func (param i32) (result i64)))
  (type $t5 (func (param i32 i32) (result i64)))
  (type $t6 (func (param i32 i32 i32 i32) (result i64)))
  (type $t7 (func (param i64 i64 i64)))
  (type $t8 (func))
  (type $t9 (func (param i32)))
  (import "x" "7" (func $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h9707cbeeb2ba72f6E (type $t0)))
  (import "v" "_" (func $_ZN17soroban_env_guest5guest3vec7vec_new17h75ae10e00f3148edE (type $t0)))
  (import "a" "3" (func $_ZN17soroban_env_guest5guest7address26authorize_as_curr_contract17h2eec93c4ba83286dE (type $t1)))
  (import "a" "0" (func $_ZN17soroban_env_guest5guest7address12require_auth17h64b56c81b7dd3f85E (type $t1)))
  (import "m" "9" (func $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17ha57004f67f23734cE (type $t2)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h689c948fe70afa08E (type $t3)))
  (import "b" "j" (func $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h04ef388afe87a798E (type $t3)))
  (import "d" "_" (func $_ZN17soroban_env_guest5guest4call4call17hceaa2bc7248df1d9E (type $t2)))
  (func $call_b (type $t3) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32) (local $l3 i64) (local $l4 i64) (local $l5 i64) (local $l6 i32) (local $l7 i64)
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
      i32.const 1048584
      call $_ZN11soroban_sdk6symbol6Symbol3new17he79a11180eb99bd7E
      local.set $l3
      local.get $l2
      call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h9707cbeeb2ba72f6E
      local.tee $l4
      i64.store offset=8
      i64.const 2
      local.set $l5
      i32.const 1
      local.set $l6
      block  ;; label = @2
        loop  ;; label = @3
          local.get $l6
          i32.eqz
          br_if 1 (;@2;)
          local.get $l6
          i32.const -1
          i32.add
          local.set $l6
          local.get $l4
          local.set $l5
          br 0 (;@3;)
        end
      end
      local.get $l2
      local.get $l5
      i64.store offset=24
      local.get $l2
      i32.const 24
      i32.add
      i32.const 1
      call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf648d4020f364708E
      local.set $l5
      call $_ZN17soroban_env_guest5guest3vec7vec_new17h75ae10e00f3148edE
      local.set $l4
      i32.const 1048576
      i32.const 8
      call $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17h843789655bab9e86E
      local.set $l7
      local.get $l2
      local.get $l3
      i64.store offset=40
      local.get $l2
      local.get $p1
      i64.store offset=32
      local.get $l2
      local.get $l5
      i64.store offset=24
      i32.const 1048636
      i32.const 3
      local.get $l2
      i32.const 24
      i32.add
      i32.const 3
      call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h281e83625d59bb8bE
      local.set $l5
      local.get $l2
      local.get $l4
      i64.store offset=16
      local.get $l2
      local.get $l5
      i64.store offset=8
      local.get $l2
      i32.const 1048684
      i32.const 2
      local.get $l2
      i32.const 8
      i32.add
      i32.const 2
      call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h281e83625d59bb8bE
      i64.store offset=32
      local.get $l2
      local.get $l7
      i64.store offset=24
      local.get $l2
      local.get $l2
      i32.const 24
      i32.add
      i32.const 2
      call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf648d4020f364708E
      i64.store offset=8
      local.get $l2
      i32.const 8
      i32.add
      i32.const 1
      call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf648d4020f364708E
      call $_ZN17soroban_env_guest5guest7address26authorize_as_curr_contract17h2eec93c4ba83286dE
      drop
      call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h9707cbeeb2ba72f6E
      local.set $l5
      i32.const 1048599
      call $_ZN11soroban_sdk6symbol6Symbol3new17he79a11180eb99bd7E
      local.set $l4
      local.get $l2
      local.get $p1
      i64.store offset=16
      local.get $l2
      local.get $l5
      i64.store offset=8
      i32.const 0
      local.set $l6
      loop  ;; label = @2
        block  ;; label = @3
          local.get $l6
          i32.const 16
          i32.ne
          br_if 0 (;@3;)
          i32.const 0
          local.set $l6
          block  ;; label = @4
            loop  ;; label = @5
              local.get $l6
              i32.const 16
              i32.eq
              br_if 1 (;@4;)
              local.get $l2
              i32.const 24
              i32.add
              local.get $l6
              i32.add
              local.get $l2
              i32.const 8
              i32.add
              local.get $l6
              i32.add
              i64.load
              i64.store
              local.get $l6
              i32.const 8
              i32.add
              local.set $l6
              br 0 (;@5;)
            end
          end
          local.get $p0
          local.get $l4
          local.get $l2
          i32.const 24
          i32.add
          i32.const 2
          call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf648d4020f364708E
          call $_ZN11soroban_sdk3env3Env15invoke_contract17h90c3f7e5c22d4c35E
          local.get $l2
          i32.const 48
          i32.add
          global.set $__stack_pointer
          i64.const 2
          return
        end
        local.get $l2
        i32.const 24
        i32.add
        local.get $l6
        i32.add
        i64.const 2
        i64.store
        local.get $l6
        i32.const 8
        i32.add
        local.set $l6
        br 0 (;@2;)
      end
    end
    unreachable
    unreachable)
  (func $_ZN11soroban_sdk6symbol6Symbol3new17he79a11180eb99bd7E (type $t4) (param $p0 i32) (result i64)
    local.get $p0
    i32.const 15
    call $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17h843789655bab9e86E)
  (func $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf648d4020f364708E (type $t5) (param $p0 i32) (param $p1 i32) (result i64)
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
    call $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h689c948fe70afa08E)
  (func $_ZN113_$LT$soroban_env_common..symbol..Symbol$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$$RF$str$GT$$GT$12try_from_val17h843789655bab9e86E (type $t5) (param $p0 i32) (param $p1 i32) (result i64)
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
    call $_ZN17soroban_env_guest5guest3buf29symbol_new_from_linear_memory17h04ef388afe87a798E)
  (func $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$19map_new_from_slices17h281e83625d59bb8bE (type $t6) (param $p0 i32) (param $p1 i32) (param $p2 i32) (param $p3 i32) (result i64)
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
    call $_ZN17soroban_env_guest5guest3map26map_new_from_linear_memory17ha57004f67f23734cE)
  (func $_ZN11soroban_sdk3env3Env15invoke_contract17h90c3f7e5c22d4c35E (type $t7) (param $p0 i64) (param $p1 i64) (param $p2 i64)
    (local $l3 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee $l3
    global.set $__stack_pointer
    block  ;; label = @1
      local.get $p0
      local.get $p1
      local.get $p2
      call $_ZN17soroban_env_guest5guest4call4call17hceaa2bc7248df1d9E
      i64.const 255
      i64.and
      i64.const 2
      i64.eq
      br_if 0 (;@1;)
      local.get $l3
      i32.const 15
      i32.add
      call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
      unreachable
    end
    local.get $l3
    i32.const 16
    i32.add
    global.set $__stack_pointer)
  (func $authorized_fn_b (type $t3) (param $p0 i64) (param $p1 i64) (result i64)
    (local $l2 i32) (local $l3 i64) (local $l4 i64) (local $l5 i32)
    global.get $__stack_pointer
    i32.const 16
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
      local.get $p0
      call $_ZN17soroban_env_guest5guest7address12require_auth17h64b56c81b7dd3f85E
      drop
      i32.const 1048584
      call $_ZN11soroban_sdk6symbol6Symbol3new17he79a11180eb99bd7E
      local.set $l3
      local.get $l2
      local.get $p0
      i64.store
      i64.const 2
      local.set $l4
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
          local.get $p0
          local.set $l4
          br 0 (;@3;)
        end
      end
      local.get $l2
      local.get $l4
      i64.store offset=8
      local.get $p1
      local.get $l3
      local.get $l2
      i32.const 8
      i32.add
      i32.const 1
      call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf648d4020f364708E
      call $_ZN11soroban_sdk3env3Env15invoke_contract17h90c3f7e5c22d4c35E
      local.get $l2
      i32.const 16
      i32.add
      global.set $__stack_pointer
      i64.const 2
      return
    end
    unreachable
    unreachable)
  (func $authorized_fn_c (type $t1) (param $p0 i64) (result i64)
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
    local.get $p0
    call $_ZN17soroban_env_guest5guest7address12require_auth17h64b56c81b7dd3f85E
    drop
    i64.const 2)
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t8)
    unreachable
    unreachable)
  (func $_ZN4core6result13unwrap_failed17h472431483d5eea7fE (type $t9) (param $p0 i32)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ (type $t8))
  (memory $memory 17)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048700))
  (global $__heap_base i32 (i32.const 1048704))
  (export "memory" (memory $memory))
  (export "call_b" (func $call_b))
  (export "authorized_fn_b" (func $authorized_fn_b))
  (export "authorized_fn_c" (func $authorized_fn_c))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base))
  (data $.rodata (i32.const 1048576) "Contractauthorized_fn_cauthorized_fn_bargscontractfn_name\00\00\00&\00\10\00\04\00\00\00*\00\10\00\08\00\00\002\00\10\00\07\00\00\00contextsub_invocations\00\00T\00\10\00\07\00\00\00[\00\10\00\0f\00\00\00"))
