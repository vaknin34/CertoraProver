contract Test {
    uint16 private constant _MAX_COPY = 100;

    function test(
        address _sender,
        address _composer,
        bytes32 _guid,
        bytes calldata _message,
        bytes calldata _extraData
    ) external payable returns (bool success, bytes memory reason) {
        bytes memory callData = abi.encodeWithSelector(
            0xd0a10260,
            _sender,
            _guid,
            _message,
            msg.sender,
            _extraData
        );
        (success, reason) = safeCall(_composer, gasleft(), msg.value, callData);
    }

    function safeCall(
        address _target,
        uint256 _gas,
        uint256 _value,
        bytes memory _calldata
    ) internal returns (bool, bytes memory) {
        // check that target has code
        uint size;
        assembly {
            size := extcodesize(_target)
        }
        if (size == 0) {
            return (false, bytes(string("no code!")));
        }

        // set up for assembly call
        uint256 _toCopy;
        bool _success;
        bytes memory _returnData = new bytes(_MAX_COPY);
        // dispatch message to recipient
        // by assembly calling "handle" function
        // we call via assembly to avoid memcopying a very large returndata
        // returned by a malicious contract
        assembly {
            _success := call(
            _gas, // gas
            _target, // recipient
            _value, // ether value
            add(_calldata, 0x20), // inloc
            mload(_calldata), // inlen
            0, // outloc
            0 // outlen
            )
        // limit our copy to 100 bytes
            _toCopy := returndatasize()
            if gt(_toCopy, _MAX_COPY) {
                _toCopy := _MAX_COPY
            }
        // Store the length of the copied bytes
        //mstore(_returnData, _toCopy)
        // copy the bytes from returndata[0:_toCopy]
        //returndatacopy(add(_returnData, 0x20), 0, _toCopy)
        }
        return (_success, _returnData);
    }


}
