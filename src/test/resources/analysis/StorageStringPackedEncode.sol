pragma experimental ABIEncoderV2;

contract Test {
    string yolo;
    function test(uint a) public returns (bytes32) {
        return keccak256(abi.encodePacked(a, yolo));
    }
}