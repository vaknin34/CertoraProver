contract struct_bug_0 {
    struct T0 { uint256 field_0;  }
    function f_5(uint256 arg_0, uint256 arg_1, uint256 arg_2) external returns (uint256 ret)
    {
        ret = arg_1;
    }

    function f_6(uint256 arg_0, uint256 arg_1, uint256 arg_2) external returns (uint256 ret)
    {
        ret = this.f_5(arg_2, arg_0, arg_2);
    }

    function f_7(uint256 arg_0, uint256 arg_1, uint256 arg_2) external returns (uint256 ret)
    {
        ret = arg_2;
    }

    function f_10(uint256 arg_0, T0 memory arg_1) external returns (uint256 ret)
    {
        uint256 arg_2 = this.f_6(arg_0, arg_0, arg_0);
        ret = this.f_5(arg_0, arg_0, arg_1.field_0);
    }

    function testFn(T0 memory arg_0) external returns (uint256 ret)
    {
        ret = this.f_10(arg_0.field_0, arg_0);
    }

    function f_12(T0 memory arg_0) external returns (uint256 ret)
    {
        ret = arg_0.field_0;
    }
}
