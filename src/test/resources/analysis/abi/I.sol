contract Test  {
    struct N { uint min; uint max; }

    struct P {
        N a;
        N b;
        N c;
        N d;
    }
    function callee(address a, address b, P memory p, bool c) public view {
    }
    function test(address a, address b, P memory p, bool c) public view {
        this.callee(a, b, p, a == b);
    }

}
