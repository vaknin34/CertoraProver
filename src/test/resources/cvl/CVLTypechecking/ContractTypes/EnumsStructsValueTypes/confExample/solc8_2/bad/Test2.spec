using Test as test;
using SuperTest as super;

rule enum_doesnt_just_get_yoinkd {
    test.EnumInAnotherContractInAFileThatsImported x; // check this is undefined
    assert true;
}


function nonEmptyInStruct(test.Yeetage structWithArray) returns bool {
    return structWithArray.inner_array.length > 0;
}
