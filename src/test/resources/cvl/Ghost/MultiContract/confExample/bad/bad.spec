using InnerContract as inner;

methods {
    function setZeroSlots(uint256,uint256) external envfree;
    function setOneSlotsAt(uint256,uint256,uint256) external envfree;
    function setZeroSlotsReversed(uint256,uint256) external envfree;
    function setOneSlotsAtReversed(uint256,uint256,uint256) external envfree;
}

sort swague;

ghost slotZero() returns uint;
ghost slotOne() returns uint;

ghost slotZeroInner() returns uint;
ghost slotOneInner() returns uint;

// currently do not support this syntax, must be a CVLImportedContract (from using statement)
// InnerContract (for now) should show up as an "undefined symbol" here
hook Sstore InnerContract.(slot 0) uint i {
    havoc slotZeroInner assuming slotZeroInner@new() == i;
}

hook Sstore swague.(slot 1)[KEY uint key] uint i {
    havoc slotOneInner assuming slotOneInner@new() == i;
}
