methods {
    function TestContract.add(uint256 a, uint256 b) internal returns (uint256) => cvl_add(a, b);
    function TestContract.double(uint256 d) internal returns (uint256) => ghost_double[d];
    function TestContract.getval() external returns (uint256) envfree;
    function TestContract.setval(uint256 newVal) external envfree;
    function TestContract.changeval() external envfree;
}

ghost mapping(uint256 => uint256) ghost_double;
ghost uint256 innerVal;

function cvl_add(uint256 a, uint256 b) returns uint256 {
    return require_uint256(a + b);
}

hook Sload uint256 contractVal val {
    require contractVal > 1;
    require innerVal == contractVal;
}

hook Sstore val uint256 contractValNew (uint256 contractValOld) {
    innerVal = contractValNew;
}

function func() returns uint256 {
    uint256 num = 10;
    uint256 ret = 20;
    require ret > num;
    return ret;
}

rule test() {
    env e;
    uint256 num = 5;
    uint256 t;
    uint256 r1 = func();
    uint256 r2 = add(e, 4, 5);
    uint256 r3 = double(e, 7);
    uint256 r4 = getval();
    require t > num;
    require t == r1;
    assert r2 == 9;
    assert r3 == 14;
    assert r4 == 1;
    assert t == num;
}

// invariant testInv() innerVal < 10 {
//     preserved setval(uint256 n) {
//         uint y;
//         require y == 4;
//         require n == 15;
//     }
//     preserved {
//         uint z;
//         require z == 3;
//     }
// }