contract Test {
  function test(uint256 a, uint256 b) public pure returns (uint256) {
      require(b != 0);
      return a/b;
  }
}
