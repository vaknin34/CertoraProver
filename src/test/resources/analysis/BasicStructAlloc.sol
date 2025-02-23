contract Test {
    struct Bar {
       uint x;
       uint y;
    }

    function test() public returns (uint) {
       Bar memory z;
       z.x = 4;
       z.y = 5;
       return z.x + z.y;
    }
}