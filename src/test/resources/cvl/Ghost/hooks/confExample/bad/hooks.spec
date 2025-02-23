methods {
    function setX(uint256) external envfree;
    function setY(uint64) external envfree;
    function setZ(uint128) external envfree;
    function setOrder(uint256) external envfree;
}
sort foo;
// X
hook Sstore misspelled_slot uint i {
    require false;
}

hook Sstore misspelled_slot_with_path[KEY uint key].(offset 32) uint i {
    require false;
}

// unaligned offset but at the end: this is fine
hook Sstore (slot 0)[KEY uint256 k].(offset 26) uint i {
    require false;
}

hook Sstore (slot 0, offset 3)[INDEX uint256 n] uint i {
    require false;
}

hook Sstore (slot 0).(offset 32)[KEY uint256 k].(offset 62)[INDEX uint256 n] uint i {
    require false;
}

rule r {
    assert true;
}
