contract Test  {
    struct S {
        address b;
        address c;
    }

    function callee(uint k, S memory moo, address x) external returns (address) {
       return (Test(x) == this ? moo.b : moo.c);
    }

    function test(S memory moo, address x) external returns (address) {
        return this.callee(123, moo, x);
    }
}
