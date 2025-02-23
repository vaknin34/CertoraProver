function min(uint256 x, uint256 y) returns bool {
    if (x < y) {
        return x;
    } else {
        return y;
    }
}

function shouldNotReturn(uint256 x, uint256 y) {
    if (x < y) {
        return x;
    } else {
        return y;
    }
}

rule shouldNotContainReturn {
    return 5;
    assert true;
}
