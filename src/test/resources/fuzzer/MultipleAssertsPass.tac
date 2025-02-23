Declarations
Variable x1 bool
Variable x2 bool
Variable h0 bool
Variable h1 bool
Variable h2 bool
Variable h3 bool
Variable h4 bool
Variable h5 bool
Variable h6 bool
Variable h7 bool
Variable int1 bv256
Variable int2 bv256
Variable int3 bv256
Variable int4 bv256
Variable int5 bv256
Variable int6 bv256
Block 0_0_0_0_0_0_0_0
AssignHavocCmd int1:bv256
AssignHavocCmd int2:bv256
AssignHavocCmd h5:bool
AssignExpCmd h0:bool Le(int1:bv256 int2:bv256)
AssumeCmd h0:bool
AssignExpCmd int3:bv256 Mul(int1:bv256 int2:bv256)
AssignExpCmd h1:bool Gt(int3:bv256 int2:bv256)
AssignHavocCmd h7:bool
JumpiCmd 1_0_0_0_0_0_0_0 2_0_0_0_0_0_0_0 h1:bool
Block 1_0_0_0_0_0_0_0
AssignExpCmd int4:bv256 Mul(int3:bv256 int2:bv256)
AssertCmd h1:bool 'FirstAssert'
AssignExpCmd int5:bv256 Mul(int1:bv256 0x11)
AssignExpCmd h2:bool Lt(int4:bv256 int5:bv256)
AssumeCmd h2:bool
JumpCmd [3_0_0_0_0_0_0_0]
Block 2_0_0_0_0_0_0_0
AssignExpCmd h3:bool LNot(h1:bool)
AssumeCmd h5:bool
AssertCmd h3:bool 'SecondAssert'
Block 3_0_0_0_0_0_0_0
AssignExpCmd h6:bool LOr(h1:bool h5:bool)
AssertCmd h6:bool '3rdAssert'
Graph
0_0_0_0_0_0_0_0 -> 1_0_0_0_0_0_0_0 2_0_0_0_0_0_0_0
1_0_0_0_0_0_0_0 -> 3_0_0_0_0_0_0_0
2_0_0_0_0_0_0_0 -> 3_0_0_0_0_0_0_0
3_0_0_0_0_0_0_0 ->
