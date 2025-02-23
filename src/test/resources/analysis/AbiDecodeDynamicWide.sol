pragma experimental ABIEncoderV2;

contract Test {
    function test(bytes memory message) public {
        (uint[] memory kind, uint64 timestamp, string memory key, uint64 value) = abi.decode(message, (uint[], uint64, string, uint64));
    }
}
