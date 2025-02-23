contract C {
    bool boolean;

    function canRevert(bool b) external {
        if (!b) { revert(); }
        boolean = b;
    }

    function cannotRevert(bool b) external {
        boolean = b;
    }

    function canRevertFromBalanceCheck(bool b) external payable {
        boolean = b;
    }

    function callCanRevertInTryCatch(bool b) external {
        try this.canRevert(b) {} catch {}
    }

    function summarizeMe(bool b) public {}
    function summarizeMeWithRevert(bool b) public {}
    function summarizeMePayable(bool b) public payable {}

    function callSummarized(bool b) public {
        this.summarizeMe(b);
    }

    function callSummarizedInTryCatch(bool b) public {
        try this.summarizeMe(b) {} catch {}
    }

    function callSummarizedWithRevert(bool b) public {
        this.summarizeMeWithRevert(b);
    }

    function callDeeperSummarized(bool b) public {
        this.callSummarized(b);
    }

    function callDeeperSummarizedWithTryCatch(bool b) public {
        try this.callSummarized(b) {} catch {}
    }

    function callSummarizedPayable(bool b) public {
        this.summarizeMePayable(b);
    }

}
