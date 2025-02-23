pragma experimental ABIEncoderV2;

contract OpenOracle {
  function put(string calldata hello) external returns (string memory) {
	return hello;
  }
}

contract Test {
  OpenOracle data;

  function test(string[] calldata arg) external returns (uint) {
    for(uint i = 0; i < arg.length; i++) {
        OpenOracle(address(data)).put(arg[i]);
    }
	return 0;
  }

}
