pragma solidity ^0.5.0;

contract FundsStorage {
	mapping(address => uint256) funds;
	
	function getFunds(address a) public returns (uint256) {
		return funds[a];
	}
	
	function update(address a, uint256 b) public {
		funds[a] = b;
	}
}