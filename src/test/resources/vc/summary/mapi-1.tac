TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	tacS!0:wordmap
	lastMsgSig:bv256
	certoraArg0:bv256
	i:bv256
	lastNumEvents:bv256
	certoraOutVar0:bv256
	certoraNumEvents:bv256
	certFunRes:bv256
	tacOrigS!0!1:wordmap
}
Program {
	Block 1_0_0_0_0_0 Succ [2_0_0_0_0_0] {
		AssignExpCmd certoraArg0 i
	}
	Block 2_0_0_0_0_0 Succ [0_0_0_1_0_5] {
		AssignHavocCmd lastMsgSig
	}
	Block 0_0_0_1_0_5 Succ [16_1024_0_1_0_6] {
		AssignExpCmd tacOrigS!0!1 tacS!0
	}
	Block 16_1024_0_1_0_6 Succ [126_1024_0_1_0_7] {
		JumpdestCmd 16_1024_0_1_0_6
	}
	Block 126_1024_0_1_0_7 Succ [148_1021_0_1_0_8] {
		JumpdestCmd 126_1024_0_1_0_7
	}
	Block 148_1021_0_1_0_8 Succ [5_0_0_0_0_0] {
		JumpdestCmd 148_1021_0_1_0_8
	}
	Block 5_0_0_0_0_0 Succ [6_0_0_0_0_0] {
		AssignExpCmd lastNumEvents certoraNumEvents
	}
	Block 6_0_0_0_0_0 Succ [] {
		AssignExpCmd certFunRes certoraOutVar0
	}
}
Axioms {
}
Metas {
}
