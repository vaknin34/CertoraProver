function fu(int16 toCast) returns int16 {
    return assert_int16(toCast * 1);
}
definition addition(uint x, uint y) returns uint = assert_uint256(x + y);

rule ComplexExp {
    uint256 sumNew;
    uint256 sumOld;
    uint256 newVal;
    uint256 oldVal;
    uint256 totVal;
    require sumNew == require_uint256(sumOld + newVal - oldVal);
    totVal = assert_uint256(sumOld + newVal - oldVal); // should pass
    assert false, "require isn't vacuous";
}

rule ToSignedInt() {
    // uint256 to int256
    uint256 toCast;
    assert assert_int256(toCast) >= 0;
}

rule AsParam {
    env e;
    uint toCast;
    uint res = require_uint256(toCast * 2);
    f(e, assert_uint256(toCast * 2));
    uint256 a = f(e, assert_uint256(toCast * 3));
    assert a >= 0;
}

rule CVLFunc {
    env e;
    int16 toCast;
    fu(toCast);
    assert false;
}

rule IfStatement {
    bool b;
    uint256 toCast;
    if (b) {
        // according to the current code, this multiply is necessary in order to
        // generate an assert command for checking the cast. This is because we generate
        // this assert only in cases where the target toType is different from the fromType.
        // toCast * 1 is mathint.
        uint ret = assert_uint256(toCast * 1);
        assert ret > 0;
    }
    assert true;
}

rule DefinitionStatement {
    uint x;
    uint y;
    uint result = addition(x, y);
    assert result >= 0;
}
