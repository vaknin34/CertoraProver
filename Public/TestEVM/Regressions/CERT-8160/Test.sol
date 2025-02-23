contract Test {
	// random hash grabbed from block 21820656
	bytes32 constant TYPEHASH = 0xe6d3208a66fcec947f446658bab06377e97655fdd664a040e5305eed7246c022;

	struct Agg {
		address token;
		uint256 amount;
	}

	function hashStructArray(Agg[] memory data) external returns (bytes32) {
		bytes32[] memory hashes = new bytes32[](data.length);
        for (uint256 i = 0; i < data.length; i++) {
            hashes[i] = keccak256(abi.encode(data[i].token, data[i].amount));
        }
        return keccak256(abi.encodePacked(hashes));
	}
}
