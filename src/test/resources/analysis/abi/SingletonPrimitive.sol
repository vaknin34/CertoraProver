contract SingletonPrimitive {
    struct T0 { address field_0; }

    function copy_address(address x) internal returns (address ret) {
        ret = address(uint160(x) / 2);
    }

    function copy_T0(T0 memory x) internal returns (T0 memory ret) {
        ret.field_0 = copy_address(x.field_0);
    }

    function f_0(address arg_0) external returns (address ret)
    {
        ret = arg_0;
    }
    function f_1(T0 calldata arg_0) external returns (address ret)
    {
        address x_0_0;
        x_0_0 = arg_0.field_0;
        ret = this.f_0(x_0_0);
    }
    function f_2(T0 memory arg_0) external returns (address ret)
    {
        T0 memory x_0_0;
        x_0_0 = copy_T0(arg_0);
        ret = this.f_1(x_0_0);
    }
    function f_3(T0 memory arg_0) external returns (address ret)
    {
        T0 memory x_0_0;
        x_0_0 = copy_T0(arg_0);
        ret = x_0_0.field_0;
    }
}
