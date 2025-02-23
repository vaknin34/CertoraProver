methods {
    function lPriv(uint256 x) external returns uint256 envfree;
    function L.priv(uint) internal returns uint => ALWAYS(6);
}

rule example(uint x) {
    assert lPriv(x) == 6, "lpriv failed";
}
