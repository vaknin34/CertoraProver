methods {
    function foo(uint256 i) external returns uint256 envfree;
    function lPriv(uint256 x) external returns uint256 envfree;
    function L.priv(uint) internal returns uint => ALWAYS(6);
}

rule for_all(uint i) {
  require (forall uint256 i . i == foo(i));
  assert i == 0;
}

rule example(uint x) {
    assert lPriv(x) == 6, "lpriv failed";
}
