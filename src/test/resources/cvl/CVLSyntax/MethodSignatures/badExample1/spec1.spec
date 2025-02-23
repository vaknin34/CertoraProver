using Impl1 as impl1;
using Impl2 as impl2;
methods {
    function impl1.getSomeUInt() external returns(uint256) envfree => ALWAYS(5) ALL; // Should not use multi-contract in summary decl.
    function impl2.getSomeUInt() external returns(uint256) => ALWAYS(4) ALL; // Should not use multi-contract in summary decl.
    function _.getSomeUInt() external returns(uint256) => ALWAYS(3) ALL; // Duplicate summary
    function _.getSomeUInt() external returns(uint256) => ALWAYS(9) ALL; // Duplicate summary
    function getSomeUInt() external returns(uint256) envfree;
    function callGetSomeUIntInImpl1() external returns(uint256) envfree;
    function callGetSomeUIntInImpl2() external returns(uint256) envfree;
}

rule checkA {
    assert callGetSomeUIntInImpl1() == 5;
}

rule checkB {
    assert callGetSomeUIntInImpl2() == 4;
}
