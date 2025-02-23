pragma experimental ABIEncoderV2;

contract Test {
    Test other;
    function test() public {
        other.takeArray(new uint[](10));
    }

    function takeArray(uint[] memory z) public {

    }
}