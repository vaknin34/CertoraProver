pragma experimental ABIEncoderV2;

contract OpenOracle {
  function put() external returns (string memory) {
	return "Hello World!";
  }
}

contract Test {
  OpenOracle data;

  function test() external returns (uint) {
	OpenOracle(address(data)).put();
	return 0;
  }
}
