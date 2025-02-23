pragma solidity ^0.5.12;

contract Dummy {
    constructor() public {

    }

    uint256 public x;
    uint64 public y;
    uint128 public z;

    uint256 public order;

    bool b;

    mapping(uint256 => bool) m;

    uint256 another;

    function setX(uint256 n) public {
        x = n;
    }

    function setY(uint64 n) public {
        y = 3 + n;
    }

    function setZ(uint128 n) public {
        z = n;
    }

    function setOrder(uint256 n) public {
        order = n;
    }

    function getB() public returns (bool) {
        return b;
    }

    function setB(bool a) public {
        b = a;
    }

    function getMAtK(uint256 k) public returns (bool) {
        return m[k];
    }

    function setMAtK(uint256 k, bool b) public {
        m[k] = b;
    }

    function setAnother(uint256 x) public {
        another = x;
    }
}