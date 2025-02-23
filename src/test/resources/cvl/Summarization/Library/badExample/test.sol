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
    function lPriv(uint x) external returns (uint) {
            return L.priv(x);
    }

    function priv(uint x) internal pure returns (uint) {
        return x;
    }

}
