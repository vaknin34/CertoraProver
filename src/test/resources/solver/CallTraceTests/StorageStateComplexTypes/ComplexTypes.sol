pragma solidity ^0.8.0;
// SPDX-License-Identifier: GPL-3.0

contract ComplexTypes {
    struct Data {
        uint256 num;
        address addr;
        mapping (uint256 => bool) innerMap;
    }

    address ownerAddr;
    bool flag;
    uint256 ui256;
    int256 i256;

    mapping (bool => bool) neg;
    mapping (address => bool) addressMap;
    mapping (uint256 => Data) dict;
    
    function test() public {
        ownerAddr = address(0x8000);
        flag = true;
        ui256 = 0x10;
        i256 = 32;

        neg[true] = false;
        neg[false] = true;

        addressMap[address(0x11)] = true;
        addressMap[address(0x22)] = false;

        dict[1].num = 100;
        dict[1].addr = address(0x140);
        dict[1].innerMap[3] = false;
        dict[1].innerMap[5] = true;

        dict[2].num = 110;
        dict[2].addr = address(0x150);
        dict[2].innerMap[7] = true;
        dict[2].innerMap[8] = false;
    }
}
