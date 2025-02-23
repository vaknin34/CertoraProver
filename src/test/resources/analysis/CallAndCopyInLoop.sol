interface Other {
    function externalPoint(uint256 amount0Out,
        uint256 amount1Out,
        address to,
        bytes calldata data) external returns (uint);
}

contract Test {
    function test(uint x, uint b) public {
        for(uint i = 0; i < b; i++) {
            bytes memory toCall = new bytes(x);
            Other(msg.sender).externalPoint(
                x, i, msg.sender, toCall
            );
        }
    }
}
