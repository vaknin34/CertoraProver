// file withdrawSuccess.spec
pragma specify 0.1;
methods {
	function getfunds(address) external returns uint256 envfree;
}

invariant address_zero_cannot_become_an_account()
            getfunds(0) == 0


rule withdraw_succeeds {
   env e; // env represents the bytecode environment passed on every call
   // invoke function withdraw and assume that it does not revert
   bool success = withdraw(e);  // e is passed as an additional argument
   assert success, "withdraw must succeed"; // verify that withdraw succeeded
}

rule transfer_reverts(address to, uint256 amount) {
    env e;
   // invoke function transfer and assume the caller is w.msg.from
   uint256 balance = getfunds@withrevert(e.msg.sender);
   transfer@withrevert(e,to,amount);
   // check that transfer reverts if the sender does not have enough funds
   assert balance < amount => lastReverted , "not enough funds";
}

rule others_can_only_increase() {
    env e;
    address other;
    method f;
    // assume msg.sender is a different address
    require e.msg.sender != other;
    // get balance before
    uint256 _balance = getfunds(other);
    // exec some method
    calldataarg arg; // any argument
	f(e,arg); // successful (potentially state-changing!)
	// get balance after
	uint256 balance_ = getfunds(other);
    // balance should not be reduced by any operation
    // can increase due to a transfer to msg.sender
	assert _balance <= balance_ ,"withdraw from others balance";
}

rule distributivityWithdraw(uint256 x, uint256 y) {

	env e;
	env eOp2;
	require(eOp2.msg.sender == e.msg.sender);
	require(currentContract != e.msg.sender);
	require(eOp2.block.timestamp == e.block.timestamp);

	storage init = lastStorage;
	require withdraw(e, x);
	require withdraw(e, y);
	uint256 balanceOp1 = ercBalance(e);
	bool res = withdraw(eOp2, require_uint256(x+y)) at init;
	require res;
	uint256 balanceOp2 = ercBalance(e);
    assert(balanceOp1==balanceOp2), "balance of withdrawer should be the same in both scenarios";
}

rule depositCorrectness {
	env e;
	env eBank;
	require eBank.msg.sender == currentContract;
	require e.msg.sender != currentContract;

	uint256 _bankBalance = ercBalance(eBank);
	uint256 _funds = getfunds(e.msg.sender);


	require e.msg.value + _bankBalance <= max_uint256;
	deposit(e, e.msg.value);

	uint256 bankBalance_ = ercBalance(eBank);
	uint256 funds_ = getfunds(e.msg.sender);

	mathint diffBankBalance = bankBalance_ - _bankBalance;
	mathint diffFunds = funds_ - _funds;

	assert assert_uint256(diffBankBalance) == e.msg.value, "Bank balance should increase by deposited amount";
	assert diffFunds == to_mathint(e.msg.value), "Depositor balance should increase by deposited amount";
}

rule depositCorrectness_repeat {
	env e;
	env eBank;
	require eBank.msg.sender == currentContract;
	require e.msg.sender != currentContract;

	storage init = lastStorage;

	uint256 _bankBalance = ercBalance(eBank);
	uint256 _funds = getfunds(e.msg.sender);

	// The following require statement is not needed, as we always implicitly assume that transferBalance
    // cannot result in balance overflow.
	//require _bankBalance + e.msg.value < 115792089237316195423570985008687907853269984665640564039457584007913129639936; // 2^256

	deposit(e, e.msg.value);

	uint256 bankBalance_ = ercBalance(eBank);
	uint256 funds_ = getfunds(e.msg.sender);

	assert assert_uint256(bankBalance_ - _bankBalance) == e.msg.value, "Bank balance should increase by deposited amount";

	deposit(e, e.msg.value) at init; // repeat
	uint256 bankBalance_2 = ercBalance(eBank);

	assert assert_uint256(bankBalance_2 - _bankBalance) == e.msg.value, "Bank balance should increase by deposited amount in repeat";
}
