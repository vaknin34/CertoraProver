
methods {
}

rule StructAccessSimple {
    bool b;
    Basic.MyStruct myStruct;
    assert myStruct.num != 8;
}
