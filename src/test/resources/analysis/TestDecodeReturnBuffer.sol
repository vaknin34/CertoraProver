pragma experimental ABIEncoderV2;

contract Test {
    function yolo() public returns (uint a, uint b) {
        a = 10;
        b = 12;
    }
    function test(uint world) public returns (uint)  {
        (bool success, bytes memory ret) = address(this).call(abi.encodeWithSignature('yolo()'));
        (uint yolo, uint swag) = abi.decode(ret, (uint, uint));
        return yolo + swag;
    }
}
