contract Test {
  function test(uint x) public {
	doThing(x, "only admin can add comp market");
  }

  function doThing(uint x, string memory message) internal {
	require(x > 0, message);
  }
}
