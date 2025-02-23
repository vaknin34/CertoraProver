// SPDX-License-Identifier: UNLICENSED
contract Test {
    struct SetPricesParams {
        Test g2;
        bytes32 k;
        uint256 signerInfo;
        address[] tokens;
    }

    function callee(SetPricesParams memory params) external {
    }

    function mid(SetPricesParams calldata params) external {
        this.callee(params);
    }

    function test(SetPricesParams memory params) external {
        this.mid(params);
    }

}
