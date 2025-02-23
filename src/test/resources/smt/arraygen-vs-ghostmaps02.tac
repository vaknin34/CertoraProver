TACSymbolTable {
    UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	    shareSum0:JSON{"name":"shareSum0","paramSorts":[{"#class":"tac.Tag.Bit256"}],"returnSort":{"#class":"tac.Tag.Bit256"},"attribute":"None","cvlResultType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.IntK","k":256},"cvlParamTypes":[{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.IntK","k":256}],"declarationName":"shareSum0"}
    	shareSum1:JSON{"name":"shareSum1","paramSorts":[{"#class":"tac.Tag.Bit256"}],"returnSort":{"#class":"tac.Tag.Bit256"},"attribute":"None","cvlResultType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.IntK","k":256},"cvlParamTypes":[{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.IntK","k":256}],"declarationName":"shareSum1"}
    	shareSum2:JSON{"name":"shareSum2","paramSorts":[{"#class":"tac.Tag.Bit256"}],"returnSort":{"#class":"tac.Tag.Bit256"},"attribute":"None","cvlResultType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.IntK","k":256},"cvlParamTypes":[{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.IntK","k":256}],"declarationName":"shareSum2"}
	}
	shareSum0:ghostmap(bv256->bv256)
	shareSum1:ghostmap(bv256->bv256)
	shareSum2:ghostmap(bv256->bv256)
	tacS!0:wordmap
	i:bv256
	x:bv256
	y:bv256
	eq:bool
	diff:bv256
	certoraOutVar0:bv256
	certFunRes:bv256
}
Program {
	Block 0_0_0_0_0_0 Succ [2_0_0_0_0_0] {
		AssignExpCmd x Select(shareSum0 i)
	}
	Block 2_0_0_0_0_0 Succ [5_0_0_0_0_0] {
		AssignExpCmd shareSum1 Store(shareSum0 i Add(x 0x5))
	}
	Block 5_0_0_0_0_0 Succ [6_0_0_0_0_0] {
		AssignExpCmd shareSum2 shareSum1
	}
	Block 6_0_0_0_0_0 Succ [] {
		AssignExpCmd y Select(shareSum2 i)
		AssignExpCmd diff Sub(y x)
		AssignExpCmd eq Eq(diff 0x5)
		AssertCmd eq ""
	}
}
Axioms {
}
Metas {
}
