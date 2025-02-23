function math(uint x, uint y) returns mathint {
    uint z;
    require x * z != 0;
    return x + y / z * x;
}

rule returnValues(uint x) {
    _ = math(x, 9);
    assert false, "intentionally fail to test call trace";
}
