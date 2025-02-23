contract Test {
    Test other;
    function test() public {
        other.noArg();
    }

    function noArg() public {

    }
}