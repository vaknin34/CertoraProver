contract Test {
    Test other;
    function test() public {
        bytes memory x = abi.encodeWithSignature("yolo(uint256)", uint(4));
        address(other).call(x);
    }

    function yolo(uint x) public {

    }
}