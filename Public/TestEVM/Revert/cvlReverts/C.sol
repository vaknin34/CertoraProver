contract C {
    bool fooWasCalled;

    function foo(bool b) external {
        fooWasCalled = true;
        if (!b) { revert(); }
    }

    function callFooFromContract(bool b) external {
        this.foo(b);
    }

    function summarizeMe(bool b) external {}
    function canRevert(bool b) external returns (bool) {
        if (!b) { revert(); }
        return b;
    }
    function callSummarizeMe(bool b) external {
        this.summarizeMe(b);
    }

    function alwaysRevertContractFun() external {
        revert();
    }
}
