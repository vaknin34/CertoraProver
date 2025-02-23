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
Block 0_0_0_0_0_0_0_0
AssignExpCmd h0:bool true
AssignExpCmd x1:bool false
JumpiCmd 1_0_0_0_0_0_0_0 2_0_0_0_0_0_0_0 h0:bool
Block 1_0_0_0_0_0_0_0
AssignExpCmd h1:bool true
AssignExpCmd h3:bool true
JumpiCmd 4_0_0_0_0_0_0_0 3_0_0_0_0_0_0_0 h1:bool
Block 2_0_0_0_0_0_0_0
AssignExpCmd h2:bool true
JumpiCmd 6_0_0_0_0_0_0_0 5_0_0_0_0_0_0_0 h2:bool
Block 3_0_0_0_0_0_0_0
AssignExpCmd h4:bool false
Block 4_0_0_0_0_0_0_0
AssignExpCmd h4:bool true
AssignExpCmd h6:bool LNot(h4:bool)
AssumeCmd h6:bool
AssignExpCmd h5:bool true
Block 5_0_0_0_0_0_0_0
AssignExpCmd h4:bool true
Block 6_0_0_0_0_0_0_0
AssignExpCmd h4:bool false
Block 148_1021_0_0_0_0_0_0
AssignExpCmd x2:bool LNot(LAnd(h3:bool h4:bool))
AssertCmd x2:bool 'simpleTAC'
Graph
0_0_0_0_0_0_0_0 -> 1_0_0_0_0_0_0_0 2_0_0_0_0_0_0_0
1_0_0_0_0_0_0_0 -> 3_0_0_0_0_0_0_0 4_0_0_0_0_0_0_0
2_0_0_0_0_0_0_0 -> 5_0_0_0_0_0_0_0 6_0_0_0_0_0_0_0
3_0_0_0_0_0_0_0 -> 148_1021_0_0_0_0_0_0
4_0_0_0_0_0_0_0 -> 148_1021_0_0_0_0_0_0
5_0_0_0_0_0_0_0 -> 148_1021_0_0_0_0_0_0
6_0_0_0_0_0_0_0 -> 148_1021_0_0_0_0_0_0
148_1021_0_0_0_0_0_0 ->
