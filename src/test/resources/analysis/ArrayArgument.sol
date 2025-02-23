pragma experimental ABIEncoderV2;

contract Data {
    function bar(uint a, uint[] memory b, uint c) public {

    }
}

contract Test {
    function test() public {
        uint[] memory z = new uint[](41);
        Data(address(0x1)).bar(10, z, 4);
    }
}