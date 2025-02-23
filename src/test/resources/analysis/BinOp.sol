contract Test {
    function test(uint x, uint y) public returns (uint) {
        uint[12] memory a = [
            x & y,
            x | y,
            x + y,
            x - y,
            x * y,
            x / y,
            x % y,
            x ** y,
            uint(int(x) / int(y)),
            uint(int(x) % int(y)),
            x << y,
            x >> y
        ];
        uint result = 0;
        for (uint i = 0; i < a.length; i++) {
            result = result ^ a[i];
        }
        return result;
    }
}
