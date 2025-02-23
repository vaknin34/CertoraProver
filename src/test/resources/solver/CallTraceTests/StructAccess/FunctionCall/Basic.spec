
methods {
    function getMyStruct(bool) external returns (Basic.MyStruct) envfree;
}

rule StructAccessFuncCall {
    bool b;
    Basic.MyStruct myStruct = getMyStruct(b);
    assert myStruct.num > 0;
}
