methods {
    function static_array_outer(bool[4] checks, TestContract.Foo input) external returns (bool) envfree;
    function dynamic_array_outer(bool[] checks, TestContract.Foo input) external returns (bool) envfree;
    function nested_outer(TestContract.Bar[] bars) external returns (bool) envfree;
}

function create_env(address addr) returns env {
    env e;
    require e.msg.sender == addr;
    return e;
}

function create_args() returns calldataarg {
    calldataarg args;
    return args;
}

function call_function_with_calldataarg(env e, calldataarg args, storage start) returns uint256 {
    return calc(e, args) at start;
}

function init_storage() returns storage {
    return lastStorage;
}

function struct_arg(TestContract.Foo input) returns TestContract.Foo {
    return input;
}

function array_arg(bool[4] arr) returns bool[4] {
    return arr;
}

function call_static_array(bool[4] arr, TestContract.Foo input) returns bool {
    return static_array_outer(arr, input);
}

function call_dynamic_array(bool[] arr, TestContract.Foo input) returns bool {
    return dynamic_array_outer(arr, input);
}

function call_string_and_bytes(string st, bytes bt) returns bool {
    env e;
    return string_and_bytes_outer(e, st, bt);
}

function call_nested_outer(TestContract.Bar[] bars) returns bool {
    return nested_outer(bars);
}

rule test_calldataarg(uint num) {
    env e = create_env(0x1000);
    calldataarg args = create_args();
    storage start = init_storage();

    assert call_function_with_calldataarg(e, args, start) != 10;
}

rule test_static_array() {
    TestContract.Foo dummy;
    TestContract.Foo input = struct_arg(dummy);
    
    bool[4] another_dummy;
    bool[4] arr = array_arg(another_dummy);

    assert call_static_array(arr, input);
}

rule test_dynamic_array() {
    TestContract.Foo dummy;
    TestContract.Foo input = struct_arg(dummy);
    
    bool[] arr;
    require arr.length == 4;

    assert call_dynamic_array(arr, input);
}

rule test_string_and_bytes() {
    string st;
    bytes bt;

    assert call_string_and_bytes(st, bt);
}

rule test_nested_array() {
    TestContract.Bar[] bars;

    assert call_nested_outer(bars);
}