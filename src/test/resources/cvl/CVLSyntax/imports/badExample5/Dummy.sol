pragma solidity ^0.5.0;

contract Dummy {

	uint256 private someUInt;
	
constructor() public {

	someUInt = 7;


}

	function getSomeUInt() public view returns(uint256) {
		return someUInt;
	}
	
	function pureCalculation(uint a, uint b) public pure returns(uint256) {
		return a+b;
	}
	
	function foo() public returns (bool) {
		return true;
	}

	function minusSevenSomeUInt() public {
		someUInt = someUInt - 7;
	}
	
	function plusSevenSomeUInt() public returns(bool) {
		someUInt = someUInt + 7;
		return true;
	}

}