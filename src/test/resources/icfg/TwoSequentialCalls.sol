contract Test {
    uint public foo;
    function swag() external {
        foo++;
    }

    function blazeit(uint x) public {
        foo+=x;
    }

    function test() public {
        this.blazeit(4);
        this.swag();
    }
}