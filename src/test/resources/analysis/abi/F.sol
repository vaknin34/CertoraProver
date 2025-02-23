// SPDX-License-Identifier: UNLICENSED

contract Test  {
    struct SetPricesParams {
        uint256 signerInfo;
        uint k;
        address[] tokens;
    }

    struct Q {
        uint a;
        address[] b;
    }

    function otherCallee(Q memory q, uint a) external returns (address) {
        return q.b[a];
    }


    function callee(uint key, SetPricesParams memory params, address keeper) public view returns (Q memory){
        Q memory q;
        q.a = key;
        q.b = new address[](params.k);
        q.b[key] = keeper;
        return q;
    }

    function mid(uint key, SetPricesParams memory params, address keeper) external returns (address){
        Q memory q = this.callee(key, params, keeper);
        return this.otherCallee(q, q.a);
    }

    function test(uint key, SetPricesParams memory params, address keeper) external returns (address) {
        return this.mid(key, params, keeper);
    }
}
