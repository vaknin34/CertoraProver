contract Test  {

        // DataStore dataStore,
        // IReferralStorage referralStorage,
        // Position.Props memory position,
        // Market.Props memory market,
        // MarketUtils.MarketPrices memory prices,
        // bool shouldValidateMinCollateralUsd
    struct N { uint min; uint max; }

    struct P {
        N a;
        N b;
        N c;
        N d;
    }

    function useThing(bool b, N memory n) public view returns (uint, uint) {
        return (0, 0);
    }

    function callee(address a, address b, P memory p, bool c) public view returns (bool, string memory) {
        uint x;
        uint y;
        (x, y) = this.useThing(p.d.min == p.b.max, p.b);
        P memory p1;
        N memory n1;
        n1.min = x;
        n1.max = y;
        p1.a = n1;
        p1.b = n1;
        p1.c = n1;
        p1.d = p.d;
        this.useThing(c, p1.a);
        if (c) {
            this.useThing(p.a.min == p.b.max, p.b);
            return (true, "true");
        }
        return (false, "");
    }
    function test(address a, address b, P memory p, bool c) public view {
        this.callee(a, b, p, a == b);
    }

}
