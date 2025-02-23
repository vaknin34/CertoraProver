Declarations
Variable b1 bool
Variable b2 bool
Variable x1 bv256
Variable x2 bv256
Block 0_0_0_0_0_0_0_0
AssignHavocCmd b1:bool
AssignHavocCmd x1:bv256
AssignExpCmd x2:bv256 Add(x1:bv256 0x1)
AssignExpCmd b2:bool Eq(x2:bv256 x1:bv256)
AssumeCmd b2:bool
JumpiCmd 1_0_0_0_0_0_0_0 2_0_0_0_0_0_0_0 b1:bool
Block 1_0_0_0_0_0_0_0
AssumeCmd true
Block 2_0_0_0_0_0_0_0
AssumeCmd true
Graph
0_0_0_0_0_0_0_0 -> 1_0_0_0_0_0_0_0 2_0_0_0_0_0_0_0
1_0_0_0_0_0_0_0 ->
2_0_0_0_0_0_0_0 ->
