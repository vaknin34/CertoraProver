interface Ext {
    function foo() external returns (uint256);
}
contract Test {
    Ext a;
    function test() external payable {
        try
        a.foo()
        {} catch Error(string memory reason) {
            revert(reason);
        } catch {
            revert();
        }
    }
}
