contract Test {
    function test(uint[2] memory foo, uint[4] memory d) public returns (uint) {
        return foo[0] + d[3];
    }
}
