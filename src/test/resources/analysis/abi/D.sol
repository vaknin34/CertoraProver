interface I {
    struct S {
        address[] a;
    }
    struct T {
        uint[] a;
    }
    function cb(T memory t, S memory s) external;
}

contract Test {
    function test(I.T memory t, address a) external {
        I.S memory s;
        I(a).cb(t, s);
    }
}
