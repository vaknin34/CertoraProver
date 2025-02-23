rule eq_return(env e, struct_bug_0.T0 x0) {
    uint256 testRet = testFn(e, x0);
    uint256 expectedRet = f_12(e, x0);
    assert(testRet == expectedRet);
}
