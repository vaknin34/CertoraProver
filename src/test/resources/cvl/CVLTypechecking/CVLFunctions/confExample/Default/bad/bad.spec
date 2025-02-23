using Test2 as theOtherContract;

methods {
    function theOtherContract.f(uint256) external returns (uint256);
}


function foo(method g) {
    env e;
    calldataarg args;
    // TODO: the expected error here should be much better
    theOtherContract.g@withrevert(e, args);
}

function baz() {
    env e;
    calldataarg args;
    g(e, args);
}

rule callerDoesntProvideParentScope(method g) {
    baz();
    assert true;
}

rule bar(method h) {
    foo(h);
    env e;
    calldataarg args;
    theOtherContract.h@withrevert(e, args);
    assert true;
}
