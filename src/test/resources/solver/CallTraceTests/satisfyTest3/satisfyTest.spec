methods {
    function mod2(uint u) external returns bool envfree;
}

rule foo() {
    uint a;

    satisfy a > 0;
    satisfy a == 0;
    satisfy a < 0;
}
