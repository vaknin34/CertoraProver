contract Test {
  address[] markets;

  function test() public {
	address[] memory _markets = markets;
	for (uint i = 0; i < _markets.length; i++) {
	  _addMarketInternal(address(_markets[i]));
	}
  }

  function _addMarketInternal(address tok) internal {
	// do nothing
  }
}
