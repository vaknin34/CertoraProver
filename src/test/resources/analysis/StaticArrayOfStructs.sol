pragma experimental ABIEncoderV2;

contract Test {
    struct Static {
        uint a;
        uint b;
        uint[5] d;
        uint c;
    }
    function test(uint n) public returns (uint) {
        Static[3][] memory alloc = new Static[3][](n);
        return abi.encode(alloc).length;
    }
}