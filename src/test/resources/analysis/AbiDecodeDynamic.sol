pragma experimental ABIEncoderV2;

contract Test {
    function test(bytes memory message) public {
        (string memory kind, uint64 timestamp, string memory key, uint64 value) = abi.decode(message, (string, uint64, string, uint64));
    }
}
