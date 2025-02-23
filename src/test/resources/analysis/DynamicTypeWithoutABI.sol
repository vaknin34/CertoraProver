contract Test {
    struct Foo {
       uint d;
    }

    function foo(uint d) external view returns (uint, address[] memory)  {
        address[] memory a = new address[](d);
        a[0] = msg.sender;
        return (d, a);
    }

    function other() external view returns(uint) {
       (uint x, address[] memory d) = this.foo(10);
       d[1] = msg.sender;
       return d.length;
    }

    function test(uint x) external view returns (uint) {
       Foo memory d = Foo({d : x});
       return d.d;
    }
}