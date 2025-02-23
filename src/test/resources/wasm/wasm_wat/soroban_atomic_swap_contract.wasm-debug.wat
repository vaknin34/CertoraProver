(module $soroban_atomic_swap_contract.wasm
  (type $t0 (func (result i64)))
  (type $t1 (func (param i64 i64) (result i64)))
  (type $t2 (func (param i64) (result i64)))
  (type $t3 (func (param i64 i64 i64) (result i64)))
  (type $t4 (func (param i32) (result i64)))
  (type $t5 (func (param i32 i32) (result i64)))
  (type $t6 (func (param i64 i64 i64 i64 i64 i64 i64)))
  (type $t7 (func (param i64 i64 i64 i64 i64)))
  (type $t8 (func))
  (type $t9 (func (param i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (type $t10 (func (param i32 i64)))
  (type $t11 (func (param i32)))
  (import "x" "7" (func $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h9707cbeeb2ba72f6E (type $t0)))
  (import "a" "_" (func $_ZN17soroban_env_guest5guest7address21require_auth_for_args17h29c4ff4d19009497E (type $t1)))
  (import "v" "g" (func $_ZN17soroban_env_guest5guest3vec26vec_new_from_linear_memory17h689c948fe70afa08E (type $t1)))
  (import "i" "8" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_hi6417h2571251124430ecdE (type $t2)))
  (import "i" "7" (func $_ZN17soroban_env_guest5guest3int16obj_to_i128_lo6417h3beaa611f07a4141E (type $t2)))
  (import "i" "6" (func $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17h7faae077db92283dE (type $t1)))
  (import "d" "_" (func $_ZN17soroban_env_guest5guest4call4call17hceaa2bc7248df1d9E (type $t3)))
  (func $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hd3caa3c785622552E (type $t4) (param $p0 i32) (result i64)
    (local $l1 i32) (local $l2 i64) (local $l3 i64) (local $l4 i64)
    global.get $__stack_pointer
    i32.const 64
    i32.sub
    local.tee $l1
    global.set $__stack_pointer
    local.get $p0
    i64.load offset=16
    local.set $l2
    local.get $p0
    i64.load offset=24
    local.set $l3
    local.get $p0
    i64.load
    local.get $p0
    i32.const 8
    i32.add
    i64.load
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17hfce1ab4e9d235057E
    local.set $l4
    local.get $l1
    local.get $p0
    i64.load offset=32
    local.get $p0
    i32.const 40
    i32.add
    i64.load
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17hfce1ab4e9d235057E
    i64.store offset=24
    local.get $l1
    local.get $l4
    i64.store offset=16
    local.get $l1
    local.get $l3
    i64.store offset=8
    local.get $l1
    local.get $l2
    i64.store
    i32.const 0
    local.set $p0
    loop (result i64)  ;; label = @1
      block  ;; label = @2
        local.get $p0
        i32.const 32
        i32.ne
        br_if 0 (;@2;)
        i32.const 0
        local.set $p0
        block  ;; label = @3
          loop  ;; label = @4
            local.get $p0
            i32.const 32
            i32.eq
            br_if 1 (;@3;)
            local.get $l1
            i32.const 32
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
        i32.const 32
        i32.add
        i32.const 4
        call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf648d4020f364708E
        local.set $l2
        local.get $l1
        i32.const 64
        i32.add
        global.set $__stack_pointer
        local.get $l2
        return
      end
      local.get $l1
      i32.const 32
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
  (func $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17hfce1ab4e9d235057E (type $t1) (param $p0 i64) (param $p1 i64) (result i64)
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
    call $_ZN17soroban_env_guest5guest3int20obj_from_i128_pieces17h7faae077db92283dE)
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
  (func $_ZN28soroban_atomic_swap_contract10move_token17ha75e7f30e0bbc826E (type $t6) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64) (param $p5 i64) (param $p6 i64)
    (local $l7 i64)
    local.get $p0
    local.get $p1
    call $_ZN17soroban_env_guest5guest7context28get_current_contract_address17h9707cbeeb2ba72f6E
    local.tee $l7
    local.get $p3
    local.get $p4
    call $_ZN11soroban_sdk5token11TokenClient8transfer17ha2a3e0898ac71e47E
    local.get $p0
    local.get $l7
    local.get $p2
    local.get $p5
    local.get $p6
    call $_ZN11soroban_sdk5token11TokenClient8transfer17ha2a3e0898ac71e47E
    block  ;; label = @1
      local.get $p4
      local.get $p6
      i64.xor
      local.get $p4
      local.get $p4
      local.get $p6
      i64.sub
      local.get $p3
      local.get $p5
      i64.lt_u
      i64.extend_i32_u
      i64.sub
      local.tee $p6
      i64.xor
      i64.and
      i64.const 0
      i64.lt_s
      br_if 0 (;@1;)
      local.get $p0
      local.get $l7
      local.get $p1
      local.get $p3
      local.get $p5
      i64.sub
      local.get $p6
      call $_ZN11soroban_sdk5token11TokenClient8transfer17ha2a3e0898ac71e47E
      return
    end
    call $_ZN4core9panicking11panic_const24panic_const_sub_overflow17hddb96f4b6b3b1af0E
    unreachable)
  (func $_ZN11soroban_sdk5token11TokenClient8transfer17ha2a3e0898ac71e47E (type $t7) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64)
    (local $l5 i32) (local $l6 i32)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l5
    global.set $__stack_pointer
    local.get $l5
    local.get $p3
    local.get $p4
    call $_ZN104_$LT$soroban_env_common..val..Val$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$i128$GT$$GT$12try_from_val17hfce1ab4e9d235057E
    i64.store offset=16
    local.get $l5
    local.get $p2
    i64.store offset=8
    local.get $l5
    local.get $p1
    i64.store
    i32.const 0
    local.set $l6
    block  ;; label = @1
      loop  ;; label = @2
        block  ;; label = @3
          local.get $l6
          i32.const 24
          i32.ne
          br_if 0 (;@3;)
          i32.const 0
          local.set $l6
          block  ;; label = @4
            loop  ;; label = @5
              local.get $l6
              i32.const 24
              i32.eq
              br_if 1 (;@4;)
              local.get $l5
              i32.const 24
              i32.add
              local.get $l6
              i32.add
              local.get $l5
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
          i64.const 65154533130155790
          local.get $l5
          i32.const 24
          i32.add
          i32.const 3
          call $_ZN84_$LT$soroban_env_guest..guest..Guest$u20$as$u20$soroban_env_common..env..EnvBase$GT$18vec_new_from_slice17hf648d4020f364708E
          call $_ZN17soroban_env_guest5guest4call4call17hceaa2bc7248df1d9E
          i64.const 255
          i64.and
          i64.const 2
          i64.ne
          br_if 2 (;@1;)
          local.get $l5
          i32.const 48
          i32.add
          global.set $__stack_pointer
          return
        end
        local.get $l5
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
    local.get $l5
    i32.const 24
    i32.add
    call $_ZN4core6result13unwrap_failed17h472431483d5eea7fE
    unreachable)
  (func $_ZN4core9panicking11panic_const24panic_const_sub_overflow17hddb96f4b6b3b1af0E (type $t8)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $swap (type $t9) (param $p0 i64) (param $p1 i64) (param $p2 i64) (param $p3 i64) (param $p4 i64) (param $p5 i64) (param $p6 i64) (param $p7 i64) (result i64)
    (local $l8 i32) (local $l9 i32) (local $l10 i64) (local $l11 i64) (local $l12 i64) (local $l13 i64)
    global.get $__stack_pointer
    i32.const 48
    i32.sub
    local.tee $l8
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
        i64.const 77
        i64.ne
        br_if 0 (;@2;)
        local.get $p2
        i64.const 255
        i64.and
        i64.const 77
        i64.ne
        br_if 0 (;@2;)
        local.get $p3
        i64.const 255
        i64.and
        i64.const 77
        i64.ne
        br_if 0 (;@2;)
        local.get $l8
        local.get $p4
        call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h1fd2ae414fbf9c1fE
        local.get $l8
        i64.load
        i64.eqz
        i32.eqz
        br_if 0 (;@2;)
        local.get $l8
        i32.const 16
        i32.add
        local.tee $l9
        i64.load
        local.set $l10
        local.get $l8
        i64.load offset=8
        local.set $l11
        local.get $l8
        local.get $p5
        call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h1fd2ae414fbf9c1fE
        local.get $l8
        i64.load
        i64.eqz
        i32.eqz
        br_if 0 (;@2;)
        local.get $l9
        i64.load
        local.set $p4
        local.get $l8
        i64.load offset=8
        local.set $l12
        local.get $l8
        local.get $p6
        call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h1fd2ae414fbf9c1fE
        local.get $l8
        i64.load
        i64.eqz
        i32.eqz
        br_if 0 (;@2;)
        local.get $l8
        i32.const 16
        i32.add
        local.tee $l9
        i64.load
        local.set $p5
        local.get $l8
        i64.load offset=8
        local.set $p6
        local.get $l8
        local.get $p7
        call $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h1fd2ae414fbf9c1fE
        local.get $l8
        i64.load
        i64.eqz
        i32.eqz
        br_if 0 (;@2;)
        local.get $p6
        local.get $l12
        i64.lt_u
        local.get $p5
        local.get $p4
        i64.lt_s
        local.get $p5
        local.get $p4
        i64.eq
        select
        br_if 1 (;@1;)
        local.get $l11
        local.get $l8
        i64.load offset=8
        local.tee $l13
        i64.lt_u
        local.get $l10
        local.get $l9
        i64.load
        local.tee $p7
        i64.lt_s
        local.get $l10
        local.get $p7
        i64.eq
        select
        br_if 1 (;@1;)
        local.get $l8
        i32.const 40
        i32.add
        local.tee $l9
        local.get $p4
        i64.store
        local.get $l8
        local.get $l12
        i64.store offset=32
        local.get $l8
        local.get $l11
        i64.store
        local.get $l8
        local.get $p3
        i64.store offset=24
        local.get $l8
        local.get $p2
        i64.store offset=16
        local.get $l8
        local.get $l10
        i64.store offset=8
        local.get $p0
        local.get $l8
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hd3caa3c785622552E
        call $_ZN17soroban_env_guest5guest7address21require_auth_for_args17h29c4ff4d19009497E
        drop
        local.get $l9
        local.get $p7
        i64.store
        local.get $l8
        local.get $l13
        i64.store offset=32
        local.get $l8
        local.get $p5
        i64.store offset=8
        local.get $l8
        local.get $p6
        i64.store
        local.get $l8
        local.get $p2
        i64.store offset=24
        local.get $l8
        local.get $p3
        i64.store offset=16
        local.get $p1
        local.get $l8
        call $_ZN60_$LT$U$u20$as$u20$soroban_sdk..env..IntoVal$LT$E$C$T$GT$$GT$8into_val17hd3caa3c785622552E
        call $_ZN17soroban_env_guest5guest7address21require_auth_for_args17h29c4ff4d19009497E
        drop
        local.get $p2
        local.get $p0
        local.get $p1
        local.get $l11
        local.get $l10
        local.get $l13
        local.get $p7
        call $_ZN28soroban_atomic_swap_contract10move_token17ha75e7f30e0bbc826E
        local.get $p3
        local.get $p1
        local.get $p0
        local.get $p6
        local.get $p5
        local.get $l12
        local.get $p4
        call $_ZN28soroban_atomic_swap_contract10move_token17ha75e7f30e0bbc826E
        local.get $l8
        i32.const 48
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
  (func $_ZN104_$LT$i128$u20$as$u20$soroban_env_common..convert..TryFromVal$LT$E$C$soroban_env_common..val..Val$GT$$GT$12try_from_val17h1fd2ae414fbf9c1fE (type $t10) (param $p0 i32) (param $p1 i64)
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
        call $_ZN17soroban_env_guest5guest3int16obj_to_i128_hi6417h2571251124430ecdE
        local.set $l3
        local.get $p1
        call $_ZN17soroban_env_guest5guest3int16obj_to_i128_lo6417h3beaa611f07a4141E
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
  (func $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E (type $t8)
    unreachable
    unreachable)
  (func $_ZN4core6result13unwrap_failed17h472431483d5eea7fE (type $t11) (param $p0 i32)
    call $_ZN4core9panicking9panic_fmt17hde8b7aa66e2831e1E
    unreachable)
  (func $_ (type $t8))
  (memory $memory 16)
  (global $__stack_pointer (mut i32) (i32.const 1048576))
  (global $__data_end i32 (i32.const 1048576))
  (global $__heap_base i32 (i32.const 1048576))
  (export "memory" (memory $memory))
  (export "swap" (func $swap))
  (export "_" (func $_))
  (export "__data_end" (global $__data_end))
  (export "__heap_base" (global $__heap_base)))
