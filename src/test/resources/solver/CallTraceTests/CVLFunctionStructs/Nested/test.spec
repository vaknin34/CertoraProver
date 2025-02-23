using TestContract as testContract;

methods {
    function workOnS1(uint x, TestContract.Complex s) external => workOnSComplexCVL(x, s);
    function workOnS2(uint x, TestContract.Complex s) external => workOnSCVL(x, s.s2);
}

function workOnSComplexCVL(uint x, TestContract.Complex s) {
    havoc testContract.m[0].s1.b1;
    require testContract.m[0].s1.b1 == (x > 3);
    havoc testContract.m[0].b3;
    require testContract.m[0].b3 == (x > 5);
}

function workOnSCVL(uint x, TestContract.Simple s) {
    require s.b1 == (x > 3);
}

rule checkWorkOnS1(uint x) {
    require x < 3;

    env e;
    workOnS1Ext(e, x);

    assert testContract.m[0].s1.b1;
}

rule checkWorkOnS1_2(uint x) {
    require x < 3;

    env e;
    workOnS1Ext(e, x);

    assert testContract.m[0].b3;
}

rule checkWorkOnS2(uint x) {
    require x < 3;

    env e;
    workOnS2Ext(e, x);

    assert testContract.m[0].s2.b1;
}

rule checkWorkOnS2_2(uint x) {
    require x < 3;

    env e;
    workOnS2Ext(e, x);

    assert testContract.m[0].b3;
}

rule checkWorkOnSCVL1(uint x) {
    require x < 3;
    TestContract.Complex s;
    workOnSCVL(x, s.s1);
    assert s.s1.b1;
}

rule checkWorkOnSCVL2(uint x) {
    require x < 3;
    TestContract.Complex s;
    workOnSCVL(x, s.s2);
    assert s.s2.b1;
}

rule checkWorkOnSCVL3(uint x) {
    require x < 3;
    TestContract.Complex s;
    workOnSComplexCVL(x, s);
    assert s.b3;
}
