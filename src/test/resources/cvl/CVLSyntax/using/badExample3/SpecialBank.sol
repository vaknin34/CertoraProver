pragma solidity ^0.5.0;

import "./FundsStorage.sol";

contract SpecialBank {
	FundsStorage fundsStorage;
	
	function transfer(address to, uint256 amount) public {
		require (msg.sender != to);
		uint256 myBalance = fundsStorage.getFunds(msg.sender);
		require (myBalance >= amount);
		uint256 recipientBalance = fundsStorage.getFunds(to);
		require (recipientBalance+amount >= amount);
		fundsStorage.update(msg.sender,myBalance-amount);
		fundsStorage.update(to,recipientBalance+amount);
	}
	

}