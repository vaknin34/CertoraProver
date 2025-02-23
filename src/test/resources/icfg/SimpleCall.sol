contract Test {
    Test other;
    function test() public {
        other.doCall(4, 5);
    }

    function doCall(uint a, uint b) public {

    }
}