pragma experimental ABIEncoderV2;

contract CalldataWithArrayScalarization {

    CalldataWithArrayScalarization c;
    uint256[] arr;
    uint256[] anotherArr;


    function testArray(uint256 x, uint256 y) public returns (uint256){
        return c.funWithMemArray(x, arr, y);
    }

    function funWithMemArray(uint256 x, uint256[] memory y, uint256 z) public returns (uint256){
        return x + y[0] + z;
    }

    function testTwoArrays(bool someBool, uint256 someUint) public {
        c.funWithTwoArrays(someBool, arr, anotherArr, someUint);
    }

    function funWithTwoArrays(bool someBool, uint256[] memory y, uint256[] calldata z, uint256 someUint) public {
        require(someUint >= 0 && someBool);
    }

    function testOnlyStaticValueTypes(bool someBool, uint256 someUint, uint8 someSmallUint) public {
        c.funWithStaticValueTypes(someBool, someUint, someSmallUint);
    }

    function funWithStaticValueTypes(bool someBool, uint256 someUint, uint8 someSmallUint) public {
        require(someUint >= 0 && someBool);
    }

}