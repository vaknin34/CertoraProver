pragma solidity ^0.8.0;

library L {
    function pub(uint x) external pure returns (uint) {
        return x;
    }
    function priv(uint x) internal pure returns (uint) {
        return x;
    }
}

contract test {
    struct Asset {
        uint256 Id;
    }

    function foo(uint256 i) public returns (uint256) {
        return i;
    }

    function foo2(uint256 i) public returns (Asset memory) {
        Asset memory asset = Asset(i);
        return asset;
    }

    function setManagedBalance(address ad, uint256 i) public {
        // do something with ad and i
    }

    function lPriv(uint x) external returns (uint) {
            return L.priv(x);
    }

    function lPub(uint x) external returns (uint) {
        return L.pub(x);
    }
}
