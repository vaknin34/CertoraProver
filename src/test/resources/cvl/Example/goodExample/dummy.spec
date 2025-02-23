methods {
    function yalla(uint x) external returns bool envfree;
}

rule zugi(uint x) {
    assert yalla(x);
}
