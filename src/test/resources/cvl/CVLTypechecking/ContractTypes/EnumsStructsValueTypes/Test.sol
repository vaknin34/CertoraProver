import './SuperTest.sol';
import './TestLibrary.sol';

contract Test is SuperTest {
    constructor() public { }

    enum EnumClaw { MountRainier, Auburn, WhiteRiver, TheClaw, Safeway }

    enum OnlyOneValue { TheOne }

    enum DuplicateEnum { Fuck, Oh, No }

    struct StructuralDamage {
        uint256 assessment;
        uint256 year;
    }

    struct SelfDeStruct {
        uint64              time_remaining;
        uint64              method;
        EnumClaw            where_to_destroy;
        StructuralDamage    damage;
		uint[][]            how_much_destroy;
    }

    struct Yeetage {
        uint256[] inner_array;
    }

    EnumClaw public my_storage_value;
    SelfDeStruct public my_struct_storage_value;

    function set_storage_from_struct(SelfDeStruct calldata x) public {
        my_storage_value = x.where_to_destroy;
    }

    function get_my_struct() public returns (SelfDeStruct memory) {
        SelfDeStruct memory ret = my_struct_storage_value;
        return ret;
    }

    function callCheckTwoStructsEqualInternal(StructuralDamage calldata x, StructuralDamage calldata y) public returns (bool) {
        return checkTwoStructsEqual(x, y);
    }

    function callCheckTwoStructsEqualExternal(StructuralDamage calldata x, StructuralDamage calldata y) public returns (bool) {
        return this.checkTwoStructsEqual(x, y);
    }

    function checkTwoStructsEqual(StructuralDamage calldata x, StructuralDamage calldata y) public returns (bool) {
        return x.assessment == y.assessment && x.year == y.year;
    }

    function checkTwoEnumsEqual(EnumClaw x, EnumClaw y) public returns (bool) {
        return x == y;
    }

    function my_storage_value_is_internal(EnumClaw x) internal returns (bool) {
        return x == my_storage_value;
    }

    function my_storage_value_is(uint8 x) public returns (bool) {
        EnumClaw e = EnumClaw(x);
        return my_storage_value_is_internal(e);
    }
}
