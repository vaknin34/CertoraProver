contract Test {
    struct Foo {
        uint d;
        uint e;
    }
    struct S {
        bool b;
        uint[][] a;
        uint[] z;
        Foo baz;
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

