methods {
    function callSummarizeMe(bool) external envfree;
    function alwaysRevertContractFun() external envfree;
    function summarizeMe(bool b) external => cvlSummarizeMe(b);
}

function cvlCanRevert(bool b) {
    if (!b) { revert("for a reason"); }
}

function cvlSummarizeMe(bool b) {
    cvlCanRevert(b);
}

rule cvlRevertCanRevert {
    bool b;
    cvlCanRevert@withrevert(b);

    satisfy lastReverted;
    satisfy !lastReverted;
    assert lastReverted <=> !b;
}

rule goingThroughSummary {
    bool b;
    callSummarizeMe@withrevert(b);

    satisfy lastReverted;
    satisfy !lastReverted;
    assert lastReverted <=> !b;
}

rule withoutWithRevertCannotRevert {
    bool b;
    cvlCanRevert(b);

    assert b; // reverting traces discarded
}


function cvlRevertWithCodeAfter(bool b) {
    if (!b) {
        revert();
    }
    assert b; // should hold here
}

rule codeAfterRevertIsSkipped {
    bool b;
    cvlRevertWithCodeAfter@withrevert(b);

    satisfy lastReverted;
    satisfy !lastReverted;
    assert lastReverted <=> !b;
}

function cvlRevertWithMultipleReasons(bool b, bool c) {
    if(!b) {
        revert("not b");
    }
    if(!c) {
        revert("b but not c");
    }
}

rule differentRevertReasons {
    bool b;
    bool c;
    cvlRevertWithMultipleReasons@withrevert(b, c);

    satisfy lastReverted && !b;
    satisfy lastReverted && b && !c;
    assert b && c => !lastReverted;
}

function alwaysRevert() {
    revert();
}

function canRevertIndirectly(bool b) {
    if(!b) {
        alwaysRevert();
    }
}

rule indirectRevert {
    bool b;
    canRevertIndirectly@withrevert(b);

    satisfy lastReverted;
    satisfy !lastReverted;
    assert lastReverted <=> !b;
}

function canRevertIndirectlyViaContract(bool b) {
    if(!b) {
        alwaysRevertContractFun();
    }
}

rule indirectRevertViaContract {
    bool b;
    canRevertIndirectlyViaContract@withrevert(b);

    satisfy lastReverted;
    satisfy !lastReverted;
    assert lastReverted <=> !b;
}


function revertInDifferentPlaces(uint n) {
    if(n == 0) {
        revert("0");
    }
    if(n < 10) {
        if(n == 1) {
            alwaysRevert();
        } else {
            if(n==2) {
                revert("2");
            }
        }
        alwaysRevert();
    }
}

rule manyRevertPaths {
    uint n;
    revertInDifferentPlaces@withrevert(n);
    satisfy lastReverted && n==0;
    satisfy lastReverted && n==1;
    satisfy lastReverted && n==2;
    satisfy lastReverted && n==3;
    assert !lastReverted <=> n >= 10;
}
