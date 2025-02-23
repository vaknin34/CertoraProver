using TestContract as testContract;

methods {
    function workOnS(uint x, TestContract.Simple s) external => workOnSCVL(x, s);
}

function workOnSCVL(uint x, TestContract.Simple s) {
    havoc testContract.m[0].b1;
    require testContract.m[0].b1 == (x > 3);
}

rule checkWorkOnS(uint x) {
    require x < 3;

    env e;
    workOnSExt(e, x);

    // xxx we do not support direct storage access on structs in a root-slot?
    assert testContract.m[0].b1;
}

rule checkWorkOnSCVL(uint x) {
    require x < 3;
    TestContract.Simple s;
    workOnSCVL(x, s);
    assert s.b1;
}
