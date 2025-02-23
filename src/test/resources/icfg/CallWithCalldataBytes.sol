contract Test {
    function test(bytes calldata theData) external returns (uint) {
        return this.accept(theData);
    }

    function accept(bytes memory theData2) public returns (uint) {
        return theData2.length;
    }
}
