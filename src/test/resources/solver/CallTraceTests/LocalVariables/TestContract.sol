pragma solidity ^0.8.4;

contract TestContract {
    uint256 val = 1;

    function add(uint256 a, uint256 b) public returns (uint256) {
        return a + b;
    }

    function double(uint256 d) public returns (uint256) {
        return 2 * d;
    }

    function getval() public returns (uint256) {
        return val;
    }

    function setval(uint256 newVal) public {
        val = newVal;
    }

    function changeval() public {
        val = add(5, 6) + double(2) + getval();
    }
}
