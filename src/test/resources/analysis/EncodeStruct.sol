contract Test {
  function test(uint x) public {
	bytes memory data = new bytes(x);
	bytes memory m = abi.encodeWithSignature("delegateToImplementation(bytes)", data);
  }
}