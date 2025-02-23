contract Test {
    struct S {
        bool b;
        uint[] a;
        bool b2;
        uint x;
        address y;
    }

    mapping (address => S[]) s;
    address key;

    function test() public returns (uint) {
        S[] memory s_ = s[key];
        return s_[2].x;
    }
}

