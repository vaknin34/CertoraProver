contract Test {
    function test(
        address token,
        address to,
        uint value
    ) public {
        functionCall(token, abi.encodeWithSelector(this.swag.selector, to, value));
    }

    function functionCall(address target, bytes memory buffer) internal {
        _functionCall(target, buffer, 0);
    }

    function _functionCall(address target, bytes memory buffer, uint value) internal {
        target.call{value: value}(buffer);
    }

    function swag(address a, uint b) public {}
}