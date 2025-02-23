methods {
    function canRevert(bool) external envfree;
    function cannotRevert(bool) external envfree;
    function callCanRevertInTryCatch(bool) external envfree;
    function callSummarized(bool) external envfree;
    function summarizeMe(bool b) external => cvlSummarizeMe(b);
}

persistent ghost bool functionEnded;
function cvlSummarizeMe(bool b) {
    functionEnded = false;
    cannotRevert(b);
    functionEnded = true;
}

persistent ghost bool callCanRevertEnded;
function callCanRevert(bool b) {
    callCanRevertEnded = false;
    canRevert(b);
    callCanRevertEnded = true;
}

persistent ghost bool hookCallWithRevert;
persistent ghost bool hookEnded;
// CVL hook that calls a Solidity function
hook Sstore currentContract.boolean bool newBoolean {
    hookEnded = false;
    if (hookCallWithRevert) {
        callCanRevert@withrevert(newBoolean);
    } else {
        callCanRevert(newBoolean);
    }
    hookEnded = true;
}

rule revertInHook(bool b) {
    hookCallWithRevert = false;
    bool originalBoolean = currentContract.boolean;
    cannotRevert@withrevert(b);
    bool newBoolean = currentContract.boolean;

    satisfy lastReverted, "there should be a reverting path";
    satisfy !lastReverted, "there should be a non-reverting path";

    assert lastReverted <=> b == false;

    assert lastReverted => originalBoolean == newBoolean;

    assert !lastReverted => newBoolean == true, "storage should be updated if there's no revert";

    assert hookEnded <=> !lastReverted;
    assert callCanRevertEnded <=> !lastReverted;
}

rule revertInHookInTryCatch(bool b) {
    hookCallWithRevert = false;
    bool originalBoolean = currentContract.boolean;
    require originalBoolean == false; // to make sure that it changed iff the inner function didn't revert.
    require hookEnded == false; // to make sure it's initially false.
    require callCanRevertEnded == false; // to make sure it's initially false.
    callCanRevertInTryCatch@withrevert(b);
    bool newBoolean = currentContract.boolean;

    assert !lastReverted;

    if (newBoolean == originalBoolean) {
        // the inner call reverted
        assert b == false;
        assert !hookEnded;
        assert !callCanRevertEnded;
    } else {
        assert b == true;
        assert hookEnded;
        assert callCanRevertEnded;
    }
}

rule revertInHookWithRevert(bool b) {
    hookCallWithRevert = true;
    bool originalBoolean = currentContract.boolean;
    require originalBoolean == false; // to make sure that it changed iff the inner function didn't revert.
    cannotRevert@withrevert(b);
    bool newBoolean = currentContract.boolean;

    assert !lastReverted;
    assert hookEnded;

    assert newBoolean == originalBoolean <=> !b;
    assert callCanRevertEnded <=> b;
}

rule revertInCVLSummaryInHook(bool b) {
    require hookEnded == false;
    callSummarized@withrevert(b);

    satisfy lastReverted, "there should be a reverting path";
    satisfy !lastReverted, "there should be a non-reverting path";
    assert hookEnded <=> !lastReverted;
    assert functionEnded <=> !lastReverted;
    assert callCanRevertEnded <=> b;
}
