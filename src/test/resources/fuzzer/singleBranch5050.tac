Declarations
Variable y1 bool
Variable y2 bool
Variable y3 bool
Variable x1 bool
Variable x2 bool
Variable h00 bool
Variable h0 bool
Variable h1 bool
Variable h2 bool
Variable h3 bool
Variable h4 bool
Block 0_0_0_0_0_0_0_0
AssignHavocCmd h0:bool
JumpiCmd 0_0_0_0_0_0_0_1 0_0_0_0_0_0_0_2 h0:bool
Block 0_0_0_0_0_0_0_1
AssignExpCmd y2:bool false
Block 0_0_0_0_0_0_0_2
AssignExpCmd y3:bool true
Block 148_1021_0_0_0_0_0_0
AssertCmd true 'simpleTAC'
Graph
0_0_0_0_0_0_0_0 -> 0_0_0_0_0_0_0_1 0_0_0_0_0_0_0_2
0_0_0_0_0_0_0_1 -> 148_1021_0_0_0_0_0_0
0_0_0_0_0_0_0_2 -> 148_1021_0_0_0_0_0_0
148_1021_0_0_0_0_0_0 ->
