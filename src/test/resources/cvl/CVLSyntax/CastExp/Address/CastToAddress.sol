// SPDX-License-Identifier: GPL-3.0

pragma solidity >=0.7.0 <0.9.0;

contract CastToAddress {
    function addressDirectToBytes(address addr) public pure returns (bytes32) {
        return bytes32(uint256(uint160(addr)));
    }    
}
