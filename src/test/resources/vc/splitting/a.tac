TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	lastMsgSig:bv256
	b:bool
	x:bv256
	y:bv256
	z:bv256
}
Program {
	Block 1_0_0_0_0_0 Succ [2_0_0_0_0_0, 3_0_0_0_0_0] {
		AssignExpCmd b Eq(x 0x0)
		JumpiCmd 2_0_0_0_0_0 3_0_0_0_0_0 b
	}
	Block 2_0_0_0_0_0 Succ [3_0_0_0_0_0] {
		AssignHavocCmd lastMsgSig
	}
	Block 3_0_0_0_0_0 Succ [4_0_0_0_0_0] {
		AssignExpCmd y Mul(0x3 x)
		JumpCmd 4_0_0_0_0_0
	}
	Block 4_0_0_0_0_0 Succ [5_0_0_0_0_0] {
		JumpCmd 5_0_0_0_0_0
	}
	Block 5_0_0_0_0_0 Succ [6_0_0_0_0_0] {
		JumpdestCmd 5_0_0_0_0_0
		JumpCmd 6_0_0_0_0_0
	}
	Block 6_0_0_0_0_0 Succ [] {
		AssignExpCmd z y
	}
}
Axioms {
}
Metas {
}
