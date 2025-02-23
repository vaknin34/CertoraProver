pragma solidity ^0.8.0;
// SPDX-License-Identifier: GPL-3.0

contract TestArray {
    function uint256DynamicArray(uint256[] calldata arr) external pure returns (uint256) {
        return arr[0];
    }

    function uint256StaticArray(uint256[3] calldata arr) external pure returns (uint256) {
        return arr[0] + arr[1] + arr[2];
    }
}

