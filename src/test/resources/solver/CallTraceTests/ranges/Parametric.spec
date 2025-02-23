rule chooseSame(env e, calldataarg arg, method f, method g) {
    int before = currentContract.n;
    f(e, arg);
    g(e, arg);
    int after = currentContract.n;
    assert before == after, "solver will find a counterexample by choosing f == g";
}

rule chooseDifferent(env e, calldataarg arg, method f, method g) {
    int before = currentContract.n;
    f(e, arg);
    g(e, arg);
    int after = currentContract.n;
    assert before != after, "solver will find a counterexample by choosing f != g";
}