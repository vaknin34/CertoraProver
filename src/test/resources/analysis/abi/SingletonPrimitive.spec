rule eq_return(env e, SingletonPrimitive.T0 x0) {
    address testRet = f_2(e, x0);
    address inlinedRet = f_3(e, x0);
    assert(testRet == inlinedRet);
}
