contract Test  {
    struct T {
        uint256 a;
        address[] b;
        bytes[] c;
        address[] d;
    }
    function callee(bytes32 key, T memory t, address goo) external {

    }
    function test(bytes32 key /* Params memory params */) external {
        T memory t;
        t.a = 100;
        t.b = new address[](10);
        t.b[1] = address(this);
        t.c = new bytes[](10);
        for (uint i = 0; i < 10; ++i) {
            t.c[i] = bytes("goo");
        }
        t.d = new address[](2);
        t.d[0] = address(this);
        this.callee(key, t, msg.sender);

    }

}
