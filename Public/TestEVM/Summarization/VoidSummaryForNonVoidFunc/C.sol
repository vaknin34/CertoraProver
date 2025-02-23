interface I {
    function returnsBool() external returns (bool);
}
contract C {
    I i;
    function foo() external returns (bool) { return i.returnsBool(); }
}
