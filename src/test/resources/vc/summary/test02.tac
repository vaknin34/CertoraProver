TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	x1:bool
	trackedVar:bool
}
Program {
	Block 0_0_0_0_0_0 Succ [1_0_0_0_0_0] {
		AssignExpCmd x1 false
	}
	Block 1_0_0_0_0_0 Succ [148_1021_0_0_0_0] {
		AssignExpCmd x1 true
	}
	Block 148_1021_0_0_0_0 Succ [] {
		AssignExpCmd trackedVar x1
	}
}
Axioms {
}
Metas {
}
