// `arr` is a dynamic array. we test that the length variable can be constrained as expected
rule LenInExpression1() {
    uint256[] arr;
    
    // XXX: this is a workaround, see comment in test below
    require arr.length * arr.length == 9; 

    assert arr.length * 2 <= 5;
}


rule CheckUint25StaticArray() {
    uint256[3] arr;
    env e;
    mathint extSum = uint256StaticArray(e, arr);
    mathint cvlSum = arr[0] + arr[1] + arr[2];
    satisfy extSum == cvlSum;
}
