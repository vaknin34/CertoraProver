pragma solidity ^0.5.12;

contract Dummy {
    constructor() public {

    }

    uint256 x;

    function init_state() public { }

    function get5() public returns (uint256) {
        return 5;
    }

    function setX(uint256 n) public {
        x = n;
    }

    function getX() public returns (uint256) {
        return x;
    }

    function getXCanRevert(uint256 n) public returns (uint256) {
        if (n < 5) {
            revert("wrong amonut");
        }
        return x;
    }

    function twoReturns(uint256 n) public returns (uint256, uint256) {
        return (x, x + n);
    }

    function threeReturns(uint256 n, uint256 m) public returns (uint256, uint256, uint256) {
        return (x, x + n, x + n + m);
    }

    function yetAnotherFunction(uint256 a, uint256 b) public returns (uint256) {
        return a % b * 2;
    }
}