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
Variable h8 bool
Variable int1 bv256
Variable int2 bv256
Variable int3 bv256
Variable int4 bv256
Variable int5 bv256
Variable int6 bv256
Variable int7 bv256
Variable int8 bv256
Variable int9 bv256
Variable int10 bv256
Block 0_0_0_0_0_0_0
AssignHavocCmd int1:bv256
AssignHavocCmd int2:bv256
AssignHavocCmd h5:bool
AssignExpCmd h0:bool Le(int1:bv256 int2:bv256)
AssumeCmd h0:bool
AssignExpCmd int3:bv256 Mul(int1:bv256 int2:bv256)
AssignExpCmd h1:bool Gt(int3:bv256 int2:bv256)
JumpiCmd 1_0_0_0_0_0_0 2_0_0_0_0_0_0 h1:bool
Block 1_0_0_0_0_0_0
AssignExpCmd int4:bv256 Mul(int3:bv256 int2:bv256)
AssignExpCmd int5:bv256 Mul(int1:bv256 0x11)
AssignExpCmd h2:bool Lt(int4:bv256 int5:bv256)
AssumeCmd h2:bool
JumpiCmd 2_0_0_0_0_0_0 3_0_0_0_0_0_0 h2:bool
Block 2_0_0_0_0_0_0
AssignExpCmd h3:bool LNot(h1:bool)
AssumeCmd h5:bool
Block 3_0_0_0_0_0_0
AssignExpCmd h6:bool LOr(h1:bool h5:bool)
AssumeCmd h6:bool
JumpiCmd 4_0_0_0_0_0_0 5_0_0_0_0_0_0 h6:bool
Block 4_0_0_0_0_0_0
AssignExpCmd int6:bv256 Mul(int3:bv256 int2:bv256)
AssignExpCmd int7:bv256 Mul(int1:bv256 0x11)
AssignExpCmd h6:bool Eq(int4:bv256 int6:bv256)
AssumeNotCmd h6:bool
JumpCmd [6_0_0_0_0_0_0]
Block 5_0_0_0_0_0_0
AssignExpCmd int8:bv256 Mul(int3:bv256 int2:bv256)
AssignExpCmd int9:bv256 Mul(int1:bv256 0x11)
AssumeNotCmd h5:bool
AssignExpCmd h7:bool Eq(int4:bv256 int6:bv256)
AssumeNotCmd h7:bool
AssertCmd h7:bool '1stAssert'
Block 6_0_0_0_0_0_0
AssignExpCmd int9:bv256 Mul(int3:bv256 int2:bv256)
AssignExpCmd int10:bv256 Mul(int1:bv256 0x11)
AssumeNotCmd h5:bool
AssertNotCmd h5:bool '2ndAssert'
Graph
0_0_0_0_0_0_0 -> 1_0_0_0_0_0_0 2_0_0_0_0_0_0
1_0_0_0_0_0_0 -> 2_0_0_0_0_0_0 3_0_0_0_0_0_0
2_0_0_0_0_0_0 -> 3_0_0_0_0_0_0
3_0_0_0_0_0_0 -> 4_0_0_0_0_0_0 5_0_0_0_0_0_0
4_0_0_0_0_0_0 -> 6_0_0_0_0_0_0
5_0_0_0_0_0_0 -> 6_0_0_0_0_0_0
6_0_0_0_0_0_0 ->


