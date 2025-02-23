contract HavocStorage {
	struct Struct {
		uint96 baz;
		bool[] bar;
		uint48[10] gorp;
	}
	
	mapping (address => Struct[6]) public a;

	function bar_value(address k, uint i) external returns (bool) {
		return a[k][i].bar[i];
	}

	function bar_length(address k, uint i) external returns (uint256) {
		return a[k][i].bar.length;
	}
}
