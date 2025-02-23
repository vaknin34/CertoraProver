contract Test {
    struct Bar {
       uint x;
       uint y;
    }

    function test() public returns (uint) {
      bytes32 hash = bytes32(uint(2));
      uint8 v = uint8(3);
      bytes32 r = bytes32(uint(4));
      bytes32 s = bytes32(uint(5));
      Bar memory z;
      z.x = 4;
      z.y = 5;
      address foo = ecrecover(hash, v, r, s);
      Bar memory w;
      w.x = uint(foo);
      w.y = 43;
      return z.x + w.y;
    }
}
