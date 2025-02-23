function func2(uint num) returns bool {
    require num != 30;
    require num != 31;
    assert num != 30;
    return num > 10;
}

function func1(uint num) returns bool {
    require num != 20;
    require num != 21;
    assert num != 20;
    uint a = require_uint256(num + 5);
    return func2(a);
}

rule CvlFunctionTest(uint num) {
    require num == 2; // for reg test
    require num != 10;
    require num != 11;
    assert num != 10;
    bool r = func1(num);
    assert r;
}
