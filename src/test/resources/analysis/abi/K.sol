contract Test {
    struct S {
        uint a;
        uint b;
    }

    bytes32 public constant K = 0x0080000000000000000000000000000000000000000000000000000000000000;

    function callee(S memory s, bytes32 k) external {}

    function test(uint k) external {
        for (uint i = 0; i < k; ++i) {
            this.callee(S(i, 420), K);
        }
    }
}
