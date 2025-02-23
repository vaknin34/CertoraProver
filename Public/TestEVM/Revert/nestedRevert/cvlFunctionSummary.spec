methods {
    function canRevert(bool) external envfree;
    function callSummarized(bool) external envfree;
    function callSummarizedInTryCatch(bool b) external envfree;
    function callSummarizedWithRevert(bool b) external envfree;
    function callSummarizedPayable(bool b) external envfree;
    function callDeeperSummarized(bool b) external envfree;
    function callDeeperSummarizedWithTryCatch(bool b) external envfree;
    function summarizeMe(bool b) external => cvlSummarizeMe(b);
    function summarizeMeWithRevert(bool b) external => cvlSummarizeMeWithRevert(b);
    function summarizeMePayable(bool b) external => cvlSummarizeMePayable(b);
}

persistent ghost bool functionEnded;
function cvlSummarizeMe(bool b) {
    functionEnded = false;
    canRevert(b);
    functionEnded = true;
}

function cvlSummarizeMeWithRevert(bool b) {
    functionEnded = false;
    canRevert@withrevert(b);
    functionEnded = true;
}

persistent ghost uint payAmount;
persistent ghost address caller;
function cvlSummarizeMePayable(bool b) {
    env e;
    require e.msg.value == payAmount;
    require e.msg.sender == caller;
    functionEnded = false;
    canRevertFromBalanceCheck(e, b);
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
    } else {
        assert revertCount == 0;
        assert b == true;
        assert functionEnded;
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
    } else {
        assert revertCount == 0;
        assert b == true;
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
    } else {
        assert revertCount == 0;
        assert b == true;
        assert functionEnded;
    }
}

rule revertInCVLSummaryBalanceCheck(bool b) {
    require revertCount == 0;
    bool originalBoolean = currentContract.boolean;
    uint callerBalance = nativeBalances[caller];
    callSummarizedPayable@withrevert(b);
    bool newBoolean = currentContract.boolean;

    satisfy lastReverted, "there should be a reverting path";
    satisfy !lastReverted, "there should be a non-reverting path";

    assert lastReverted <=> callerBalance < payAmount, "revert should happen exactly when caller cannot pay";
    assert lastReverted <=> !functionEnded, "in case of revert the cvl function summary shouldn't reach the end";

    assert lastReverted => originalBoolean == newBoolean, "storage shouldn't change if there was a revert";
    assert lastReverted => revertCount == 1, "only `callSummarizedPayable` triggers the REVERT hook";

    assert !lastReverted => newBoolean == b, "storage should be updated if there's no revert";
}

rule twoRevertingCalls(bool b1, bool b2) {
    require revertCount == 0;
    bool originalBoolean = currentContract.boolean;
    callSummarized@withrevert(b1);
    bool newBoolean1 = currentContract.boolean;
    bool firstCallReverted = lastReverted;

    satisfy firstCallReverted, "there should be a reverting path";
    satisfy !firstCallReverted, "there should be a non-reverting path";

    assert firstCallReverted <=> !b1, "revert should depend only on value of b";
    assert firstCallReverted <=> !functionEnded, "in case of revert the cvl function summary shouldn't reach the end";

    assert firstCallReverted => originalBoolean == newBoolean1, "storage shouldn't change if there was a revert";
    assert firstCallReverted => revertCount == 2, "both `canRevert` and `callSummarized` should trigger the REVERT hook";

    assert !firstCallReverted => b1 == true, "Only the `b == true` case doesn't revert";
    assert !firstCallReverted => newBoolean1 == true, "storage should be updated if there's no revert";

    mathint oldRevertCount = revertCount;
    callSummarized@withrevert(b2);
    bool newBoolean2 = currentContract.boolean;
    bool secondCallReverted = lastReverted;

    satisfy secondCallReverted, "there should be a reverting path";
    satisfy !secondCallReverted, "there should be a non-reverting path";

    satisfy firstCallReverted && !secondCallReverted, "the reverts should be independent";
    satisfy !firstCallReverted && secondCallReverted, "the reverts should be independent";

    assert secondCallReverted <=> !b2, "revert should depend only on value of b";
    assert secondCallReverted <=> !functionEnded, "in case of revert the cvl function summary shouldn't reach the end";

    assert secondCallReverted => newBoolean1 == newBoolean2, "storage shouldn't change if there was a revert";
    assert secondCallReverted => revertCount == oldRevertCount + 2, "both `canRevert` and `callSummarized` should trigger the REVERT hook";

    assert !secondCallReverted => b2 == true, "Only the `b == true` case doesn't revert";
    assert !secondCallReverted => newBoolean2 == true, "storage should be updated if there's no revert";
}
