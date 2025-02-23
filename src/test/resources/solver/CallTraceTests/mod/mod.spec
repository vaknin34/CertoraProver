methods {
    function mod2(uint u) external returns bool envfree;
}

rule even(uint256 u){
    assert mod2(u), "not even";
}
