methods {
    function canRevert(bool) external envfree;
    function callSummarized(bool) external envfree;
    function callSummarizedInTryCatch(bool b) external envfree;
    function callSummarizedWithRevert(bool b) external envfree;
    function callDeeperSummarized(bool b) external envfree;
    function callDeeperSummarizedWithTryCatch(bool b) external envfree;
    function summarizeMe(bool b) external => cvlSummarizeMe(b);
    function summarizeMeWithRevert(bool b) external => cvlSummarizeMeWithRevert(b);
}

persistent ghost bool functionEnded;
function cvlSummarizeMe(bool b) {
    functionEnded = false;
    callCanRevert(b);
    functionEnded = true;
}

persistent ghost bool callCanRevertEnded;
function callCanRevert(bool b) {
    callCanRevertEnded = false;
    canRevert(b);
    callCanRevertEnded = true;
}

function cvlSummarizeMeWithRevert(bool b) {
    functionEnded = false;
    callCanRevert@withrevert(b);
    functionEnded = true;
}

persistent ghost mathint revertCount;
hook REVERT(uint offset, uint size) {
    revertCount = revertCount + 1;
}

rule revertInCVLSummary(bool b) {
    require revertCount == 0;
    bool originalBoolean = currentContract.boolean;
    callSummarized@withrevert(b);
    bool newBoolean = currentContract.boolean;

    satisfy lastReverted, "there should be a reverting path";
    satisfy !lastReverted, "there should be a non-reverting path";

    assert lastReverted <=> !b, "revert should depend only on value of b";
    assert lastReverted <=> !functionEnded, "in case of revert the cvl function summary shouldn't reach the end";
    assert lastReverted <=> !callCanRevertEnded, "in case of revert the inner cvl function shouldn't reach the end";

    assert lastReverted => originalBoolean == newBoolean, "storage shouldn't change if there was a revert";
    assert lastReverted => revertCount == 2, "both `canRevert` and `callSummarized` should trigger the REVERT hook";

    assert !lastReverted => b == true, "Only the `b == true` case doesn't revert";
    assert !lastReverted => newBoolean == true, "storage should be updated if there's no revert";
}

rule withoutWithRevertNeverReverts(bool b) {
    require revertCount == 0;
    bool originalBoolean = currentContract.boolean;
    callSummarized(b);
    bool newBoolean = currentContract.boolean;

    assert b, "we should not see any traces where b is false, as those would revert";
    assert functionEnded, "the cvl function summary should reach the end";
    assert callCanRevertEnded, "the inner cvl function should reach the end";
    assert revertCount == 0, "we should not trigger the REVERT hook";
    assert newBoolean == true, "storage should be updated if there's no revert";
}

rule revertInCVLSummaryInTryCatch(bool b) {
    require revertCount == 0;
    bool originalBoolean = currentContract.boolean;
    require originalBoolean == false; // to make sure that it changed iff the inner function didn't revert.
    callSummarizedInTryCatch@withrevert(b);
    bool newBoolean = currentContract.boolean;

    assert !lastReverted;
    if (newBoolean == originalBoolean) {
        // the inner call reverted
        assert revertCount == 1;
        assert b == false;
        assert !functionEnded;
        assert !callCanRevertEnded;
    } else {
        assert revertCount == 0;
        assert b == true;
        assert functionEnded;
        assert callCanRevertEnded;
    }
}

rule revertInCVLSummaryWithRevert(bool b) {
    require revertCount == 0;
    bool originalBoolean = currentContract.boolean;
    require originalBoolean == false; // to make sure that it changed iff the inner function didn't revert.
    callSummarizedWithRevert@withrevert(b);
    bool newBoolean = currentContract.boolean;

    assert !lastReverted;
    assert functionEnded;
    if (newBoolean == originalBoolean) {
        // the inner call reverted
        assert revertCount == 1;
        assert b == false;
        assert !callCanRevertEnded;
    } else {
        assert revertCount == 0;
        assert b == true;
        assert callCanRevertEnded;
    }
}

rule revertInCVLSummaryDeeplyCalled(bool b) {
    require revertCount == 0;
    bool originalBoolean = currentContract.boolean;
    callDeeperSummarized@withrevert(b);
    bool newBoolean = currentContract.boolean;

    satisfy lastReverted, "there should be a reverting path";
    satisfy !lastReverted, "there should be a non-reverting path";

    assert lastReverted <=> !b, "revert should depend only on value of b";
    assert lastReverted <=> !functionEnded, "in case of revert the cvl function summary shouldn't reach the end";
    assert lastReverted <=> !callCanRevertEnded, "in case of revert the inner cvl function shouldn't reach the end";

    assert lastReverted => originalBoolean == newBoolean, "storage shouldn't change if there was a revert";
    assert lastReverted => revertCount == 3, "both `canRevert`, `callSummarized` and `callDeeperSummarized` should trigger the REVERT hook";

    assert !lastReverted => b == true, "Only the `b == true` case doesn't revert";
    assert !lastReverted => newBoolean == true, "storage should be updated if there's no revert";
}

rule revertInCVLSummaryDeeplyCalledInTryCatch(bool b) {
    require revertCount == 0;
    bool originalBoolean = currentContract.boolean;
    require originalBoolean == false; // to make sure that it changed iff the inner function didn't revert.
    callDeeperSummarizedWithTryCatch@withrevert(b);
    bool newBoolean = currentContract.boolean;

    assert !lastReverted;
    if (newBoolean == originalBoolean) {
        // the innermost call reverted
        assert revertCount == 2, "both `canRevert` and `callSummarized` should trigger the REVERT hook";
        assert b == false;
        assert !functionEnded;
        assert !callCanRevertEnded;
    } else {
        assert revertCount == 0;
        assert b == true;
        assert functionEnded;
        assert callCanRevertEnded;
    }
}
