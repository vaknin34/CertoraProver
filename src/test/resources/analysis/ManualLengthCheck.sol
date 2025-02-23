contract Test {
    function test(bytes memory signature, bytes32 hash) public returns (address) {
        if(signature.length == 68) {
            bytes32 r;
            bytes32 s;
            uint8 v;
            assembly {
                r := mload(add(signature, 0x20))
                s := mload(add(signature, 0x40))
                v := byte(0, mload(add(signature, 0x60)))
            }
            return ecrecover(hash, v, r, s);
        } else {
            return msg.sender;
        }
    }
}
