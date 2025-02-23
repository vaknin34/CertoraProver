methods {
    function test() external envfree;
}

rule check1() {
    test();
    assert false;
}
