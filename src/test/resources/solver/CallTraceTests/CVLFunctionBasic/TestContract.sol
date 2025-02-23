pragma solidity ^0.8.4;

contract TestContract {
    struct Foo {
        uint256 field_int;
        bool field_bool;
        address field_addr;
    }

    function calc(uint256 a, uint256 b, bool op) public pure returns (uint256) {
        if (op) {
            return a + b;
        } else {
            return a - b;
        }
    }

    function complex_args(bool[2] memory checks, Foo memory input) external pure returns (bool) {
        return checks[0] && checks[1] && input.field_bool && input.field_int > 10 && input.field_addr != address(0) && false;
    }
}
