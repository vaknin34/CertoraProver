TACSymbolTable {
    UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	i1:bv256
	i2:bv256
	i3:bv256
	b1:bool
	b2:bool
	b3:bool
	b4:bool
}
Program {
	Block 0_0_0_0_0_0 Succ [3_0_0_0_0_0] {
		AssignHavocCmd i1
		AssignHavocCmd i2
	}
	Block 3_0_0_0_0_0 Succ [8_0_0_0_0_0] {
		AssignExpCmd b1 LNot(Eq(i1 i2))
		AssumeCmd b1
		AssignExpCmd b2 LNot(Eq(i1 i3))
		AssignExpCmd b3 LNot(Eq(i2 i3))
		AssignExpCmd b4 LOr(b2 b3)
	}
	Block 8_0_0_0_0_0 Succ [] {
		AssignExpCmd i3 i2
		AssertCmd:0 b4 ""
	}
}
Axioms {
}
Metas {
	"0": [
        {
            "key": {
            "name": "cvl.user.defined.assert",
            "type": "tac.MetaMap$Companion$NothingValue",
            "erasureStrategy": "Canonical"
            },
            "value": {
            }
        }
    ]
}
