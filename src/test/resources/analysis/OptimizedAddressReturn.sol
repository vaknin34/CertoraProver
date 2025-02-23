contract Test {
    function getMarketsExt() external returns (address[] memory) {
        return new address[](0);
    }

    function getMarkets() internal returns (address[] memory) {
        return this.getMarketsExt();
    }

    function test() public returns (uint) {
        return getMarkets().length;
    }
}
