
using FundsStorage as funds;

// testing a successfully resolved contract, but calling a function that doesn't exist

methods {
	function funds.getFunds(address) external returns uint256 envfree;
}

rule transferDistrubitive(uint256 a1, uint256 a2, address to) {
	uint256 _bal = funds.getFunds_missing(to);

	storage init = lastStorage;

	env e;
	transfer(e,to,a1);
	transfer(e,to,a2);
	uint256 bal1_ = funds.getFunds_missing(to);

	transfer(e, to, require_uint256(a1 + a2)) at init;

	uint256 bal2_ = funds.getFunds_missing2(to);

	assert bal1_ == bal2_ , "transfer should be distributive with respect to amount";
}
