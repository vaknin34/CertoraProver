using Test as test;

methods {
    function callCheckTwoStructsEqualInternal(test.StructuralDamage calldata x, test.StructuralDamage calldata y) internal returns bool => yeet(x, y);
    function get_my_struct() internal returns (test.SelfDeStruct memory) => yote();
}

ghost takes_a_struct(test.SelfDeStruct) returns bool;

function yeet(test.StructuralDamage x, test.StructuralDamage y) returns bool {
    return x == y;
}

function yote() returns test.SelfDeStruct {
    test.SelfDeStruct yotify;
    return yotify;
}

rule two_different_enum_types(test.EnumClaw x, test.EnumInASuperContract y) {
    assert x == y;
}

rule enum_and_int(test.EnumClaw x) {
    test.EnumClaw y = 7;
    assert 5 == x;
}
