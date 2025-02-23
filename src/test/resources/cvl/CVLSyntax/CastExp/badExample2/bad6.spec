rule numLitVsInt() {
    // syntax error as numberLiteral is out of safety bounds
    int256 i1 = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff; // 2^256 - 1
    assert true;
}

rule numLitVsUint() {
    // syntax error as numberLiteral is out of safety bounds
    uint256 u1 = 0x10000000000000000000000000000000000000000000000000000000000000000; // 2^256
    assert true;
}

