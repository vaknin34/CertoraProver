contract Test {

    struct N { uint min; uint max; }

    struct P {
        N a;
        N b;
        N c;
        N d;
    }

    function useThing(N memory n) public view {
    }

    function test(N memory p) public view returns (string memory) {
        this.useThing(p);
        return ("boop");
    }
}
