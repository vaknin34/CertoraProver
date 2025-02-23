TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	t:bool
	x1:bv256
}
Program {
	Block 0_0_0_0_0_0 Succ [] {
		AssignExpCmd t Gt(x1 0x0)
		AssumeCmd t
		AssignExpCmd x1 0x20
	}
}
Axioms {
}
Metas {
}
