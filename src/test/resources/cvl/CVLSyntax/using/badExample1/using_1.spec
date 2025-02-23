
using FundsStorage3 as funds;


methods {
	function funds.getFunds(address) external returns uint256 envfree;
}

rule tryToAccessNoneExistingContract() {
	address a = funds;
	assert true;
}
