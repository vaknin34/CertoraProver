pragma experimental ABIEncoderV2;

contract Test {

    struct InitialPath {
        address tokenIn;
        address pool;
        address tokenOut;
        bool preFunded;
        uint256 amountIn; // 0 amountIn implies pre-funding
        bytes context;
    }

    struct PercentagePath {
        address tokenIn;
        address pool;
        address tokenOut;
        uint64 balancePercentage; // Multiplied by 10^6
        bytes context;
    }

    struct Output {
        address token;
        address to;
        bool unwrapBento;
        uint256 minAmount;
    }

    struct ComplexPathParams {
        uint256 deadline;
        InitialPath[] initialPath;
        PercentagePath[] percentagePath;
        Output[] output;
    }

    function test(ComplexPathParams memory yeet) public returns (uint) {
        return this.otherTest(yeet);
    }

    function otherTest(ComplexPathParams memory foo) public returns (uint) {
        return foo.initialPath.length;
    }
}
