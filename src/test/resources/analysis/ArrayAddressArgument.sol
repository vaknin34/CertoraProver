pragma experimental ABIEncoderV2;

contract Data {
    function bar(uint a, address[] memory b, uint c) public {

    }
}

contract Test {
    function test() public {
        Data(address(0x1)).bar(10, new address[](41), 4);
    }
}
