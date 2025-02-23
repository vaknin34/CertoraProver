pragma solidity ^0.8.0;

contract test {
    struct MyStruct {
        uint256 myInt;
    }

    function fooInt(int x) external returns (int) {
        return x;
    }

    function fooUInt(uint x) external returns (uint) {
        return x;
    }

    function fooBool(bool x) external returns (bool) {
        return x;
    }

    function fooAddress(address x) external returns (address) {
        return x;
    }

    function fooString(string memory x) external returns (string memory) {
        return x;
    }

    function fooBytes(bytes memory x) external returns (bytes memory) {
        return x;
    }

    function fooArray() external returns (uint[] memory) {
        uint[] memory arr = new uint[](3);
        arr[0] = 1;
        arr[1] = 2;
        arr[2] = 3;
        return arr;
    }

    function fooArrayInt() external returns (int[] memory) {
        int[] memory arr = new int[](3);
        arr[0] = 1;
        arr[1] = 2;
        arr[2] = 3;
        return arr;
    }

    function fooStruct() external returns (MyStruct memory) {
        MyStruct memory myStruct = MyStruct(42);
        return myStruct;
    }
}

