pragma experimental ABIEncoderV2;

contract Test {
    function test(uint n) public returns (uint) {
        uint[] memory yolo = new uint[](n);
        uint[][3] memory yeet = [yolo, yolo, yolo];
        bytes memory x = abi.encode(yeet, yeet);
        return x.length;
    }
}
