// SPDX-License-Identifier: UNLICENSED
contract C {
    mapping (bytes32 => bool) boolValues;

    function getBool(bytes32 key) external view returns (bool) {
        return boolValues[key];
    }
}

contract Test {
    struct SetPricesParams {
        C c;
        bytes32 k;
        uint256 signerInfo;
        address[] tokens;
    }

    struct T {
        uint256 hi;
        uint256 low;
    }
    struct S {
        bool b;
        bytes32 key;
        T t;
        uint256[] boop;
    }

    bytes32 public constant A1 = keccak256(abi.encode("A1"));
    bytes32 public constant A2 = keccak256(abi.encode("A2"));

    struct B {
        bool b1;
        bool b2;
    }
    function get(C c, bytes32 key) external view returns (B memory) {
        B memory b;
        b.b1 = c.getBool(keccak256(abi.encode(key, A1)));
        b.b2 = c.getBool(keccak256(abi.encode(key, A2)));
        return b;
    }

    function callee(SetPricesParams memory params) external returns (S memory) {
        S memory ret;
        T memory t;
        B memory b = this.get(params.c, params.k);
        t.hi = params.signerInfo;
        t.low = params.signerInfo;
        ret.key = params.k;
        ret.b = b.b1;
        ret.t = t;
        ret.boop = new uint256[](params.signerInfo);

        return ret;
    }

    function mid(SetPricesParams calldata params) external {
        this.callee(params);
    }

    function test(SetPricesParams memory params) external {
        this.mid(params);
    }

}
