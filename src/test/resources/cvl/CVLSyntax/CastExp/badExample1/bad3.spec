methods {
    function to_uint256(int256, int256) external returns(uint256) envfree;
}
//CVLTODO: fix the test after enable contract function with the same name as cast function
// Currently, no casting to/from non-numeric types
rule castingBools() {
    uint256 x = to_uint256(true);
    assert true;
}

rule castingFromBools() {
    bool b = assert_bool(1);
    assert true;
}

// this should throw an overloading error when
// we cannot find a function with same signature
// in the contract
rule runFromContract() {
    int256 x1 = 1;
    int256 x2 = 5;
    int256 x3 = 10;

    uint256 ux2 = to_uint256(x1, x2, x3);
    assert ux2 == 1;
}
