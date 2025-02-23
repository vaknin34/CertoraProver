contract Test {
    function test(bytes memory signature) public returns (uint) {
        (bytes32 r, bytes32 s, uint8 v) = abi.decode(signature, (bytes32, bytes32, uint8));
        return 0;
    }
}
