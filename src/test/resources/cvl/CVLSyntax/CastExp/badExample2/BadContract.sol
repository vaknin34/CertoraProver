pragma solidity ^0.5.12;

contract BadContract {

    function to_uint256(int256 x) public returns(uint256) {
        return 42;
    }

    function to_uint256(int256 x1, int256 x2) public returns(uint256) {
        return uint256(x1+x2);
    }
}
