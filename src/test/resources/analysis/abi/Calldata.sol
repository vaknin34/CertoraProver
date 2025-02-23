// SPDX-License-Identifier: UNLICENSED

pragma experimental ABIEncoderV2;

contract Test {
    function do_a_write(uint256[] memory p) public pure {
       p[3] = 3;
    }

    function intermediary1(uint256[] calldata p) external view {
        this.do_a_write(p);
    }

    function test(uint256[] memory p) public view {
        this.intermediary1(p);
    }
}
