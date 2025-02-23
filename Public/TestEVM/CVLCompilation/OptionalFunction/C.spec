methods {
    function foo() external envfree;
    function foo() internal => f();
    function bar() external envfree;
    function bar() internal => g();
    function baz() external envfree;
    function baz() internal => h();
    function nonExisting() external returns (uint) envfree optional;
    function nonExistingMultipleReturn() external returns (uint, uint) envfree optional;
}

function f() {
    nonExisting();
}

function g() {
    uint x = nonExisting();
}

function h() {
    uint x; uint y;
    (x, y) = nonExistingMultipleReturn();
}

rule r {
    foo();
    assert true;
}

rule r2 {
    bar();
    assert true;
}

rule r3 {
    baz();
    assert true;
}
