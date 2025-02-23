contract MethodOverloading {
	uint128 x;
	function getRekt() external {
       x++;
    }

	function getRekt(uint256 t) external {
       x++;
    }

    function getRekt(string memory t) external {
       x++;
    }

    function getRektCalldata(string calldata t) external {
       x++;
    }
}
