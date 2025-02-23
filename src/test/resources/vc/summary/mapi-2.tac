TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	lastMsgSig:bv256
	lastNumEvents:bv256
	certoraOutVar0:bv256
	certoraNumEvents:bv256
	certFunRes:bv256
}
Program {
	Block 0_0_0_0_0_0 Succ [16_1024_0_3_0_13] {
		AssignHavocCmd lastMsgSig
	}
	Block 16_1024_0_3_0_13 Succ [126_1024_0_3_0_14] {
		JumpdestCmd 16_1024_0_3_0_13
	}
	Block 126_1024_0_3_0_14 Succ [148_1021_0_3_0_15] {
		JumpdestCmd 126_1024_0_3_0_14
	}
	Block 148_1021_0_3_0_15 Succ [18_0_0_0_0_0] {
		JumpdestCmd 148_1021_0_3_0_15
		AssignHavocCmd lastMsgSig
	}
	Block 18_0_0_0_0_0 Succ [19_0_0_0_0_0] {
		AssignExpCmd lastNumEvents certoraNumEvents
	}
	Block 19_0_0_0_0_0 Succ [] {
		AssignExpCmd certFunRes certoraOutVar0
	}
}
Axioms {
}
Metas {
}
