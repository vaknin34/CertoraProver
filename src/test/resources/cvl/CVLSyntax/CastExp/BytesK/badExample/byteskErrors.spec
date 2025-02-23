methods {
    function from_bytes() external returns (bytes1) => ALWAYS(to_bytes1(-1));
}

rule signedNumericCastError() {
   bytes1 b1 = to_bytes1(-5);
}

rule numericOutOfBoundsError() {
   bytes1 b1 = to_bytes1(99999999999999999999999);
}

rule nonNumberLiteralSuppliedError() {
    uint256 u1 = 42;
    bytes1 b1 = to_bytes1(u1);
}
