pragma solidity ^0.8.4;

contract TestContract {
    struct Foo {
        uint256 field_int;
        bool field_bool;
        address field_addr;
        bytes field_bytes;
    }

    struct Bar {
        Foo foo;
        uint256[] dyn_arr;
        bool[2] static_arr;
    }

    function calc(uint256 a, uint256 b, bool op) public pure returns (uint256) {
        if (op) {
            return a + b;
        } else {
            return a - b;
        }
    }

    function static_array_inner(bool[4] memory checks, Foo memory input) internal pure returns (bool) {
        return checks[0] && checks[2] && input.field_bool && input.field_int > 10 && input.field_addr != address(0) && input.field_bytes.length > 0 && false;
    }

    function static_array_outer(bool[4] memory checks, Foo memory input) external pure returns (bool) {
        return static_array_inner(checks, input);
    }

    function dynamic_array_inner(bool[] memory checks, Foo memory input) internal pure returns (bool) {
        return checks[0] && checks[3] && input.field_bool && input.field_int > 10 && input.field_addr != address(0) && input.field_bytes.length > 0 && false;
    }

    function dynamic_array_outer(bool[] memory checks, Foo memory input) external pure returns (bool) {
        return dynamic_array_inner(checks, input);
    }

    function string_and_bytes_inner(string memory st, bytes memory bt) internal pure returns (bool) {
        return keccak256(bytes(st)) == keccak256(bt);
    }

    function string_and_bytes_outer(string memory st, bytes memory bt) external pure returns (bool) {
        return string_and_bytes_inner(st, bt);
    }

    function sum_odds_static_inner(uint256[4] memory nums) internal pure returns (uint256) {
        return nums[1] + nums[3];
    }

    function sum_odds_static_outer(uint256[4] memory nums) external pure returns (uint256) {
        return sum_odds_static_inner(nums);
    }

    function sum_odds_dynamic_inner(uint256[] memory nums) internal pure returns (uint256) {
        return nums[1] + nums[3];
    }

    function sum_odds_dynamic_outer(uint256[] memory nums) external pure returns (uint256) {
        return sum_odds_dynamic_inner(nums);
    }

    function nested_inner(Bar[] memory bars) internal pure returns (bool) {
        return bars[0].dyn_arr[2] == 3 && bars[1].static_arr[0] && bars[2].foo.field_addr != address(0);
    }
    
    function nested_outer(Bar[] memory bars) external pure returns (bool) {
        return nested_inner(bars);
    }
}
