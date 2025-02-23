methods {
    function _.returnsBool() external => voidCVL() expect void;
}
function voidCVL() {
    assert false;
}

rule r {
    env e;
    foo(e);
    assert true;
}
