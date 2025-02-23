contract Test {
    Test other;
    function test() public {
        uint[] memory z = new uint[](10);
        bytes memory x = abi.encodeWithSignature("yolo(uint256,uint256[])", uint(4), z);
        address(other).call(x);
    }

    function yolo(uint x, uint[] memory y) public {

    }
}