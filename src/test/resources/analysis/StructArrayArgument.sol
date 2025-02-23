pragma experimental ABIEncoderV2;

contract Test {
    struct Yeet {
        uint a;
        uint b;
        bytes data;
    }
    function test(Yeet[] memory arg) public returns (uint) {
        return arg.length;
    }
}
