pragma solidity ^0.8.0;

contract Basic {

    MyStruct ms;

    struct MyStruct {
        uint256 num;
    }

    function getMyStruct(bool b) external returns (MyStruct memory) {
        if (b) {
            ms.num = ms.num + 1;
        }
        return ms;
    }
}
