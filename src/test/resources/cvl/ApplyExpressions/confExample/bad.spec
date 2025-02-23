methods {
    function get5() external returns uint envfree;
    function setX(uint256) external envfree;
    function getX() external returns uint envfree;
    function getXCanRevert(uint256) external returns uint envfree;
}

ghost my_ghost(uint256) returns bool;

definition my_def(uint256 x) returns bool = x >= 5;

function callGet5() {
    assert get5() == 5;
}

rule defNotCommand(uint x) {
    my_def(x);
    assert true;
}

rule ghostNotCommand(uint x) {
    my_ghost(x);
    assert true;
}
