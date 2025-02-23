contract Test {
    mapping(uint => bytes) s;

    function test(uint k) external returns (bytes32) {
        bytes storage entry = s[k];
        return doThing(entry) ^ doThing(entry);
    }

    function doThing(bytes memory k) internal returns (bytes32) {
        return keccak256(k);
    }
}
