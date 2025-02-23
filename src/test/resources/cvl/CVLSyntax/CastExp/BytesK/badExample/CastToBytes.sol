pragma solidity ^0.5.12;

contract CastToBytes {
    function from_bytes() public returns (bytes1) {
        return 0x05;
    }

    function from_bytes(bytes1 b) public returns (bytes1) {
        return b;
    }
}
