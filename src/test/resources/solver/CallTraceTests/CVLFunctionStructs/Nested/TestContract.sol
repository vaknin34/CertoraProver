pragma solidity ^0.8.4;

contract TestContract {
    struct Complex {
        Simple s1;
        Simple s2;
        bool b3;
    }

    struct Simple {
        uint x;
        address y;
        uint8 z1;
        uint8 z2;
        bool b1;
        uint x2;
        bool b2;
    }

    mapping (uint => Complex) m;

    function workOnS1Ext(uint x) external {
        this.workOnS1(x, m[0]);
    }

    function workOnS2Ext(uint x) external {
        this.workOnS2(x, m[0]);
    }

    function workOnS1(uint x, Complex memory s) external {
        s.s1.x = x;
        s.s1.b2 = true;
        s.s1.b1 = x > 3;
        s.b3 = x > 5;
    }

    function workOnS2(uint x, Complex memory s) external {
        s.s2.x = x;
        s.s2.b2 = true;
        s.s2.b1 = x > 3;
        s.b3 = x > 5;
    }

}
