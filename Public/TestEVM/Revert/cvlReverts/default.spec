methods {
    function foo(bool) external envfree;
    function callFooFromContract(bool) external envfree;
    function callSummarizeMe(bool) external envfree;
    function canRevert(bool) external returns bool envfree;
    function summarizeMe(bool b) external => cvlSummarizeMe(b);
}

function cvlSummarizeMe(bool b) {
    callWithRevertingMethodInArg(b);
}

function callWithRevertingMethodInArg(bool b) {
    baz(canRevert(b));
}

ghost bool bazCalled;
function baz(bool b) {
    bazCalled = true;
}

persistent ghost bool functionEnded;
function callFoo(bool b) {
    functionEnded = false;
    foo(b);
    functionEnded = true;
}

persistent ghost bool reachedAfterCallFoo;
function callCallFoo(bool b) {
    reachedAfterCallFoo = false;
    callFoo(b);
    reachedAfterCallFoo = true;
}

function callWithRevertDeeper(bool b) returns bool {
    callFoo@withrevert(b);
    return lastReverted;
}

function callWithRevertDeeperContractFun(bool b) returns bool {
    callFooFromContract@withrevert(b);
    return lastReverted;
}

rule withRevertCanRevert {
    bool b;
    callFoo@withrevert(b);
    satisfy lastReverted;
}

rule codeAfterNonRevertingCallUnreachable {
    bool b;
    require !b;
    callFoo(b);
    assert false;
}

rule withRevertAlwaysReverts {
    bool b;
    callFoo@withrevert(b);
    assert lastReverted; // should fail
}

rule contractFunctionVersionForComparison {
    require !currentContract.fooWasCalled;
    bool b;
    callFooFromContract@withrevert(b);
    satisfy lastReverted;
    assert currentContract.fooWasCalled <=> !lastReverted;
}

rule withRevertRevertsInCorrectCase {
    require !currentContract.fooWasCalled;
    bool b;
    callFoo@withrevert(b);
    assert b <=> !lastReverted;
    assert currentContract.fooWasCalled <=> !lastReverted;
    assert functionEnded <=> !lastReverted;
}

rule deeperWithRevertCanRevert {
    bool b;
    bool reverted = callWithRevertDeeper(b);
    satisfy reverted;
}

rule deeperWithRevertRevertsInCorrectCase {
    bool b;
    bool reverted = callWithRevertDeeper(b);
    assert b <=> !reverted;
    assert functionEnded <=> !reverted;
}

rule deeperWithRevertContractFun {
    bool b;
    bool reverted = callWithRevertDeeperContractFun(b);
    satisfy reverted;
}

rule moreIndirectRevertCanRevert {
    bool b;
    callCallFoo@withrevert(b);
    satisfy lastReverted;
}

rule moreIndirectRevertRevertsCorrectly {
    require !currentContract.fooWasCalled;
    bool b;
    callCallFoo@withrevert(b);
    assert b <=> !lastReverted;
    assert currentContract.fooWasCalled <=> b;
    assert reachedAfterCallFoo <=> b;
    assert functionEnded <=> b;
}

rule callAsArgInSummary {
    bool b;
    require !bazCalled;
    callSummarizeMe@withrevert(b);
    satisfy lastReverted;
    satisfy !lastReverted;
    assert bazCalled <=> !lastReverted;
}
