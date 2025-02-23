contract Test {
    struct Params {
        uint[] b1;
        uint[][] c;
        address y;
    }

    struct OtherParams {
        uint256 a;
    }

    function callee(bytes32 key, Params memory params) public view returns (OtherParams memory) {
        OtherParams memory out;
        return out;
    }

    function test(bytes32 key, Params memory params) external {
        OtherParams memory out = this.callee(key, params);
    }

}
