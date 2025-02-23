methods {
	function getfunds(address) external returns uint256 envfree;
}

invariant address_zero_cannot_become_an_account()
            getfunds(0) == 0;
