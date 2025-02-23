rule invalidCast1() {
    // syntax error casting from address to uint256 is invalid
    env e;
    address adrs = e.msg.sender;
    uint256 x = assert_uint256(adrs);
    assert true;
}

rule invalidCast2() {
    // syntax error casting from bool to uint256 is invalid
    uint256 x = assert_uint256(true);
    assert true;
}

rule invalidCast3() {
    // syntax error casting from array to uint256 is invalid
    bytes32[] arr;
    uint256 x = assert_uint256(arr);
    assert true;
}

rule invalidCast4() {
    // syntax error casting from bytesk to uint256 is invalid
    bytes1 one_byte;
    uint256 x = assert_uint256(one_byte);
    assert true;
}

rule invalidCast5() {
    // syntax error casting from uint256 to bytesk is invalid
    uint256 x;
    bytes1 one_byte = to_bytes1(x);
    assert true;
}






