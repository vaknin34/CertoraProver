contract Test  {
    struct A {
        uint[] a;
    }
    struct S {
        uint t;
        A a;
    }
    function callee(S memory s) external returns (uint256) { }
    function test(uint t, A memory a) external returns (uint256) {
        return this.callee(S(t, a));
    }
}
