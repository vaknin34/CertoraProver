TACSymbolTable {
	UserDefined {
		UninterpSort skey
	}
	BuiltinFunctions {
		to_skey:JSON{"#class":"vc.data.TACBuiltInFunction.Hash.ToSkey"}
		skey_basic:JSON{"#class":"vc.data.TACBuiltInFunction.Hash.Basic"}
		safe_math_narrow_bv256:JSON{"#class":"vc.data.TACBuiltInFunction.SafeMathNarrow","returnSort":{"bits":256}}
	}
	UninterpretedFunctions {
		CANON111:JSON{"name":"CANON111","paramSorts":[{"#class":"tac.Tag.Int"}],"returnSort":{"#class":"tac.Tag.Int"},"attribute":"Ghost","cvlResultType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlParamTypes":[{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}],"declarationName":"CANON111"}
		CANON84:JSON{"name":"CANON84","paramSorts":[{"#class":"tac.Tag.Int"}],"returnSort":{"#class":"tac.Tag.Int"},"attribute":"Ghost","cvlResultType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlParamTypes":[{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}],"declarationName":"CANON84"}
		CANON92:JSON{"name":"CANON92","paramSorts":[],"returnSort":{"#class":"tac.Tag.Int"},"attribute":"Ghost","cvlResultType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlParamTypes":[],"declarationName":"CANON92"}
	}
	tacM0x40@2:bv256:0
	tacM0x40@5:bv256:0
	tacM0x40@7:bv256:0
	tacCodesizeCANON0:bv256:1
	tacCalldatabufCANON0@2:bv256:2
	tacCalldatabufCANON0@5:bv256:2
	tacCalldatabufCANON1@2:bv256:3
	CANON85!!73:int:4
	CANON85!!85:int:4
	tacM0x40!!0:bv256:0
	tacM0x40!!1:bv256:0
	tacM0x40!!2:bv256:0
	tacAddress!!31:bv256:5
	tacAddress!!57:bv256:5
	tacAddress!!76:bv256:5
	lastReverted:bool:6
	tacExtcodesize!!4:wordmap:7
	CANON88!!8:bv256:8
	tacCalldatasize@2:bv256:9
	tacCalldatasize@5:bv256:9
	tacCalldatasize@7:bv256:9
	calledContract:int:10
	tacExtcodesize:wordmap:7
	CANON100:bool:11
	CANON101:int
	CANON102:int
	CANON103:bool:11
	CANON104:int
	CANON105:int
	CANON106:bool
	CANON107:int
	CANON108:bool:12
	CANON109:bool:11
	CANON111:ghostmap(int->int)
	tacCalldatasize!!28:bv256:9
	tacCalldatasize!!54:bv256:9
	tacCalldatasize!!74:bv256:9
	tacBalance:wordmap:13
	calledContract!!42:int:10
	calledContract!!67:int:10
	tacBalance!!36:wordmap:13
	tacBalance!!40:wordmap:13
	tacBalance!!62:wordmap:13
	tacBalance!!5:wordmap:13
	tacCalldatabuf@2:bytemap:14
	tacCalldatabuf@5:bytemap:15
	tacCalldatabuf@7:bytemap:16
	CANON59!!53:int:17
	CANON59!!72:int:17
	R3:bv256:1
	R6:bv256:18
	R9:bv256:19
	B18:bool:20
	B19:bool:20
	B22:bool
	B79:bool:12
	B80:bool
	B88:bool
	B97:bool:12
	I20:int
	I21:int
	I23:int
	I24:int
	I25:int
	I26:int
	I35:int:20
	I38:int:20
	I43:int
	I44:int
	I45:int
	I46:int
	I51:int
	I52:int
	I61:int:20
	I64:int:20
	I68:int
	I81:int
	I86:int
	I87:int
	I89:int
	I90:int
	I91:int
	I92:int
	I93:int
	I94:int
	I96:int
	R10:bv256:21
	R11:bv256:22
	R12:bv256:23
	R16:bv256:20
	R17:bv256:20
	R29:bv256:20
	R32:bv256:20
	R33:bv256:20
	R34:bv256:20
	R37:bv256:20
	R39:bv256:20
	R41:bv256:20
	R47:bv256:24
	R55:bv256:20
	R58:bv256:20
	R59:bv256:20
	R60:bv256:20
	R63:bv256:20
	R65:bv256:20
	R66:bv256:20
	R69:bv256:24
	R75:bv256:20
	R77:bv256:20
	R78:bv256:18
	R82:bv256:24
	CANON28!7:ghostmap(bv256*bv256*bv256->bv256):25
	tacAddress@2:bv256:5
	tacAddress@5:bv256:5
	tacAddress@7:bv256:5
	LCANON0@2:bv256:24
	LCANON1@5:bv256:24
	LCANON2@7:bv256:18
	LCANON3@7:bv256:24
	CANON10:int:26
	CANON11:int:27
	CANON12:int:28
	CANON13:int:29
	CANON14:int:30
	CANON15:int:31
	CANON16:int:32
	CANON17:int:33
	CANON18:int
	CANON19:int
	CANON20:bool
	CANON21:int
	CANON22:int:34
	CANON23:int
	CANON24:int
	CANON25:int
	CANON26:int:35
	CANON28:ghostmap(bv256*bv256*bv256->bv256):25
	CANON29:bv256:20
	CANON42:bv256:20
	CANON43:bv256:20
	CANON44:bv256:20
	CANON45:bv256:20
	CANON46:int:20
	CANON47:bv256:20
	CANON48:int:20
	CANON49:bv256:20
	CANON50@2:bv256:20
	CANON50@5:bv256:20
	CANON50@7:bv256:20
	CANON51:int:36
	CANON52:int:37
	CANON53:int
	CANON54:int
	CANON55:int
	CANON56:int
	CANON57:int
	CANON58:int
	CANON59:int:17
	CANON61:bv256:20
	CANON74:bv256:20
	CANON75:bv256:20
	CANON76:bv256:20
	CANON77:bv256:20
	CANON78:int:20
	CANON79:bv256:20
	CANON80:int:20
	CANON81:bv256:20
	CANON82:int:38
	CANON83:int:39
	CANON84:ghostmap(int->int):40
	CANON85:int:4
	CANON87:bv256:20
	CANON88:bv256:8
	CANON89:bool:12
	CANON90:bool
	CANON92:int:41
	CANON93:int
	CANON94:bool:11
	CANON95:int
	CANON96:int
	CANON97:bool
	CANON98:int
	CANON99:int
	tacContractAtCANON1:bv256:19
	tacContractAtCANON2:bv256:21
	tacContractAtCANON3:bv256:22
	lastHasThrown:bool:42
	lastReverted!!49:bool:6
	lastReverted!!71:bool:6
	lastReverted!!84:bool:6
	CANON1:bv256:20
	CANON2:bool:20
	CANON3:bool:20
	CANON4:int:43
	CANON5:int:44
	CANON6:int:45
	CANON7:int:46
	CANON8:int:47
	CANON9:int:48
	tacContractAtCANON:bv256:23
	CANON26!!27:int:35
	CANON26!!50:int:35
	lastHasThrown!!30:bool:42
	lastHasThrown!!48:bool:42
	lastHasThrown!!56:bool:42
	lastHasThrown!!70:bool:42
	lastHasThrown!!83:bool:42
	tacSighash!!13:bv256:49
	tacSighash!!14:bv256:49
	tacSighash!!15:bv256:49
	tacSighash@2:bv256:49
	tacSighash@5:bv256:49
	tacSighash@7:bv256:49
	CANON:bv256:20
	CANON106!!95:bool:11
}
Program {
	Block 0_0_0_0_0_0 Succ [1_0_0_1_0_1] {
		AssignHavocCmd tacM0x40!!0:0
		AssumeExpCmd Le(tacM0x40!!0:0 0x80 )
		AssignHavocCmd tacM0x40!!1:0
		AssumeExpCmd Le(tacM0x40!!1:0 0x80 )
		AssignHavocCmd tacM0x40!!2:0
		AssumeExpCmd Le(tacM0x40!!2:0 0x80 )
		AssignHavocCmd R3:1
		AssignHavocCmd tacExtcodesize!!4:7
		AssignHavocCmd tacBalance!!5:13
		AssignHavocCmd R6:18
		AssignHavocCmd CANON10:26
		AssumeExpCmd LAnd(Ge(CANON10:26 0x0(int) ) Le(CANON10:26 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON11:27
		AssumeExpCmd LAnd(Ge(CANON11:27 0x0(int) ) Le(CANON11:27 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON12:28
		AssumeExpCmd LAnd(Ge(CANON12:28 0x0(int) ) Le(CANON12:28 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON13:29
		AssumeExpCmd LAnd(Ge(CANON13:29 0x0(int) ) Le(CANON13:29 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON15:31
		AssumeExpCmd Eq(CANON15:31 0x14(int) )
		AssignHavocCmd CANON28!7:25
		AssignHavocCmd CANON84:40
		AssignHavocCmd CANON88!!8:8
		AssumeExpCmd Ge(CANON88!!8:8 0x2 )
		AssignHavocCmd CANON92:41
		AssumeExpCmd LAnd(Ge(CANON92:41 0x2(int) ) Le(CANON92:41 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd R9:19
		AssumeExpCmd Eq(R9:19 0x1 )
		AssignHavocCmd R10:21
		AssumeExpCmd Eq(R10:21 0x2 )
		AssignHavocCmd R11:22
		AssumeExpCmd Eq(R11:22 0x4 )
		AssignHavocCmd CANON4:43
		AssumeExpCmd LAnd(Ge(CANON4:43 0x0(int) ) Le(CANON4:43 0xffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON5:44
		AssumeExpCmd Eq(CANON5:44 0x0(int) )
		AssignHavocCmd CANON6:45
		AssumeExpCmd LAnd(Ge(CANON6:45 0x0(int) ) Le(CANON6:45 0xffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON7:46
		AssumeExpCmd LAnd(Ge(CANON7:46 0x0(int) ) Le(CANON7:46 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON8:47
		AssumeExpCmd LAnd(Ge(CANON8:47 0x0(int) ) Le(CANON8:47 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON9:48
		AssumeExpCmd LAnd(Ge(CANON9:48 0x0(int) ) Le(CANON9:48 0xffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd R12:23
		AssumeExpCmd LAnd(Ge(R12:23 0x1 ) Le(R12:23 0xffffffffffffffffffffffffffffffffffffffff ) )
		AssignHavocCmd tacSighash!!13:49
		AssumeExpCmd Eq(tacSighash!!13:49 0x771602f7 )
		AssignHavocCmd tacSighash!!14:49
		AssumeExpCmd Eq(tacSighash!!14:49 0xeee97206 )
		AssignHavocCmd tacSighash!!15:49
		AssumeExpCmd Eq(tacSighash!!15:49 0x31b6bd06 )
		AnnotationCmd:50 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"Setup"}}
		AnnotationCmd:51 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"multi contract setup"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1}
		AnnotationCmd:52 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"rule parameters setup"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":2}
		AnnotationCmd:53 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"contract address vars initialized"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":3}
		AnnotationCmd:54 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"setup read tracking instrumentation"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":4}
		AnnotationCmd:55 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"last storage initialize"}}
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageGlobalChangeSnippet.StorageTakeSnapshot","lhs":{"namePrefix":"lastStorage","tag":{"#class":"tac.Tag.BlockchainState"},"callIndex":0,"meta":[{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule"}},{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry","name":"lastStorage"}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.VMInternal.BlockchainState"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"lastStorage"}]}}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":5}
		AnnotationCmd:56 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"assuming contracts in scene with non-empty bytecode have EXTCODESIZE larger than zero"}}
		AssignExpCmd R16:20 Select(tacExtcodesize!!4:7 Apply(to_skey:bif R12:23) )
		AssumeExpCmd Ge(R16:20 0x1 )
		AssignExpCmd R17:20 Select(tacExtcodesize!!4:7 Apply(to_skey:bif R12:23) )
		AssumeExpCmd Eq(R17:20 R3:1 )
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":6}
		AnnotationCmd:57 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"assuming address(0).code has no code deployed"}}
		AssignExpCmd B19:20 Eq(Select(tacExtcodesize!!4:7 Apply(skey_basic:bif 0x0) ) 0x0 )
		AssumeCmd B19:20
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":7}
		AnnotationCmd:58 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"assumptions about contracts' addresses"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":8}
		AnnotationCmd:59 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"assumptions about static addresses"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":9}
		AnnotationCmd:60 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"establish addresses of precompiled contracts"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":10}
		AnnotationCmd:61 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"assumptions about uniqueness of contracts' addresses"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":11}
		AnnotationCmd:62 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"static links"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":12}
		AnnotationCmd:63 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"record starting nonces"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":13}
		AnnotationCmd:64 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"cloned contracts have no balances"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":14}
		AnnotationCmd:65 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"Linked immutable setup"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":15}
		AnnotationCmd:66 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"Constrain immutables"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":16}
		AnnotationCmd:67 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"establish equivalence of extension and base contract immutables"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":17}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":0}
		AnnotationCmd:68 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Declaration","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":32,"charByteOffset":4},"end":{"line":32,"charByteOffset":10}},"cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"id":"e","scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AnnotationCmd JSON{"key":{"name":"cvl.trace.declaration","type":"spec.CVLCompiler$Companion$TraceMeta$VariableDeclaration","erasureStrategy":"Erased"},"value":{"v":{"#class":"spec.CVLCompiler.Companion.TraceMeta.ValueIdentity.CVLVar","id":"e230"},"t":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"type":{"#class":"spec.CVLCompiler.Companion.TraceMeta.DeclarationType.Variable"},"fields":[[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"coinbase"}],{"namePrefix":"CANON9","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":32,"charByteOffset":4},"end":{"line":32,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.coinbase"}]},[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"basefee"}],{"namePrefix":"CANON7","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":32,"charByteOffset":4},"end":{"line":32,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.basefee"}]},[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"timestamp"}],{"namePrefix":"CANON13","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":32,"charByteOffset":4},"end":{"line":32,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.timestamp"}]},[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"blobbasefee"}],{"namePrefix":"CANON8","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":32,"charByteOffset":4},"end":{"line":32,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.blobbasefee"}]},[{"#class":"tac.DataField.StructField","field":"tx"},{"#class":"tac.DataField.StructField","field":"origin"}],{"namePrefix":"CANON6","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":32,"charByteOffset":4},"end":{"line":32,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.tx.origin"}]},[{"#class":"tac.DataField.StructField","field":"msg"},{"#class":"tac.DataField.StructField","field":"sender"}],{"namePrefix":"CANON4","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":32,"charByteOffset":4},"end":{"line":32,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.msg.sender"}]},[{"#class":"tac.DataField.StructField","field":"msg"},{"#class":"tac.DataField.StructField","field":"value"}],{"namePrefix":"CANON5","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":32,"charByteOffset":4},"end":{"line":32,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.msg.value"}]},[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"difficulty"}],{"namePrefix":"CANON10","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":32,"charByteOffset":4},"end":{"line":32,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.difficulty"}]},[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"gaslimit"}],{"namePrefix":"CANON11","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":32,"charByteOffset":4},"end":{"line":32,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.gaslimit"}]},[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"number"}],{"namePrefix":"CANON12","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":32,"charByteOffset":4},"end":{"line":32,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.number"}]}]}}
		AnnotationCmd:69 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":18}
		AnnotationCmd:70 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Definition","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":33,"charByteOffset":4},"end":{"line":33,"charByteOffset":20}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"idL":[{"#class":"spec.cvlast.CVLLhs.Id","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":33,"charByteOffset":4},"end":{"line":33,"charByteOffset":15}},"id":"num","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":33,"charByteOffset":4},"end":{"line":33,"charByteOffset":15}}}}],"exp":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"5","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"5"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":33,"charByteOffset":18},"end":{"line":33,"charByteOffset":19}}}},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AssignExpCmd:71 CANON14:30 0x5
		AnnotationCmd:72 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":19}
		AnnotationCmd:73 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Declaration","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":34,"charByteOffset":4},"end":{"line":34,"charByteOffset":14}},"cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"id":"t","scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AnnotationCmd JSON{"key":{"name":"cvl.trace.declaration","type":"spec.CVLCompiler$Companion$TraceMeta$VariableDeclaration","erasureStrategy":"Erased"},"value":{"v":{"#class":"spec.CVLCompiler.Companion.TraceMeta.ValueIdentity.TACVar","t":{"namePrefix":"CANON15","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":34,"charByteOffset":4},"end":{"line":34,"charByteOffset":14}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"t"}]}},"t":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"type":{"#class":"spec.CVLCompiler.Companion.TraceMeta.DeclarationType.Variable"},"fields":null}}
		AnnotationCmd:74 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":20}
		AnnotationCmd:75 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Definition","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":35,"charByteOffset":4},"end":{"line":35,"charByteOffset":24}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"idL":[{"#class":"spec.cvlast.CVLLhs.Id","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":35,"charByteOffset":4},"end":{"line":35,"charByteOffset":14}},"id":"r1","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":35,"charByteOffset":4},"end":{"line":35,"charByteOffset":14}}}}],"exp":{"#class":"spec.cvlast.CVLExp.ApplyExp.CVLFunction","id":"func","args":[],"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":35,"charByteOffset":17},"end":{"line":35,"charByteOffset":23}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.CVLFunction","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":24,"charByteOffset":0},"end":{"line":29,"charByteOffset":1}},"declarationId":"func","params":[],"rets":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"block":[{"cmd_type":"spec.cvlast.CVLCmd.Simple.Definition","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":25,"charByteOffset":4},"end":{"line":25,"charByteOffset":21}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"idL":[{"#class":"spec.cvlast.CVLLhs.Id","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":25,"charByteOffset":4},"end":{"line":25,"charByteOffset":15}},"id":"num","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":null,"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":25,"charByteOffset":4},"end":{"line":25,"charByteOffset":15}}}}],"exp":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"a","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":null,"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":25,"charByteOffset":18},"end":{"line":25,"charByteOffset":20}}}},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}},{"cmd_type":"spec.cvlast.CVLCmd.Simple.Definition","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":26,"charByteOffset":4},"end":{"line":26,"charByteOffset":21}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"idL":[{"#class":"spec.cvlast.CVLLhs.Id","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":26,"charByteOffset":4},"end":{"line":26,"charByteOffset":15}},"id":"ret","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":null,"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":26,"charByteOffset":4},"end":{"line":26,"charByteOffset":15}}}}],"exp":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"14","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":null,"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":26,"charByteOffset":18},"end":{"line":26,"charByteOffset":20}}}},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}},{"cmd_type":"spec.cvlast.CVLCmd.Simple.AssumeCmd.Assume","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":27,"charByteOffset":4},"end":{"line":27,"charByteOffset":22}},"exp":{"#class":"spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp","l":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"ret","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":null,"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":27,"charByteOffset":12},"end":{"line":27,"charByteOffset":15}}},"twoStateIndex":"NEITHER"},"r":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"num","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":null,"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":27,"charByteOffset":18},"end":{"line":27,"charByteOffset":21}}},"twoStateIndex":"NEITHER"},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":null,"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":27,"charByteOffset":12},"end":{"line":27,"charByteOffset":21}}}},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}},{"cmd_type":"spec.cvlast.CVLCmd.Simple.Return","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":28,"charByteOffset":4},"end":{"line":28,"charByteOffset":15}},"exps":[{"#class":"spec.cvlast.CVLExp.VariableExp","id":"ret","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":null,"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":28,"charByteOffset":11},"end":{"line":28,"charByteOffset":14}}},"twoStateIndex":"NEITHER"}],"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}],"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}},"noRevert":true},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
	}
	Block 1_0_0_1_0_1 Succ [2_0_0_0_0_0] {
		AnnotationCmd:76 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.CVLFunctionStart","callIndex":1,"name":"func","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":35,"charByteOffset":17},"end":{"line":35,"charByteOffset":23}},"isNoRevert":true}}
		AnnotationCmd:77 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Definition","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":25,"charByteOffset":4},"end":{"line":25,"charByteOffset":21}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"idL":[{"#class":"spec.cvlast.CVLLhs.Id","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":25,"charByteOffset":4},"end":{"line":25,"charByteOffset":15}},"id":"num","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":25,"charByteOffset":4},"end":{"line":25,"charByteOffset":15}}}}],"exp":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"a","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"a"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":25,"charByteOffset":18},"end":{"line":25,"charByteOffset":20}}}},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AssignExpCmd:78 CANON16:32 0xa
		AnnotationCmd:79 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":22}
		AnnotationCmd:80 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Definition","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":26,"charByteOffset":4},"end":{"line":26,"charByteOffset":21}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"idL":[{"#class":"spec.cvlast.CVLLhs.Id","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":26,"charByteOffset":4},"end":{"line":26,"charByteOffset":15}},"id":"ret","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":26,"charByteOffset":4},"end":{"line":26,"charByteOffset":15}}}}],"exp":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"14","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"14"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":26,"charByteOffset":18},"end":{"line":26,"charByteOffset":20}}}},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AssignExpCmd:81 CANON17:33 0x14
		AnnotationCmd:82 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":23}
		AnnotationCmd:83 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.AssumeCmd.Assume","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":27,"charByteOffset":4},"end":{"line":27,"charByteOffset":22}},"exp":{"#class":"spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp","l":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"ret","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":27,"charByteOffset":12},"end":{"line":27,"charByteOffset":15}}},"twoStateIndex":"NEITHER"},"r":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"num","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":27,"charByteOffset":18},"end":{"line":27,"charByteOffset":21}}},"twoStateIndex":"NEITHER"},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":27,"charByteOffset":12},"end":{"line":27,"charByteOffset":21}}}},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AssignExpCmd:84 I20 0x14(int)
		AssignExpCmd:85 I21 0xa(int)
		AssignExpCmd:86 B22 true
		AnnotationCmd:87 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":24}
		AssignExpCmd:88 I23 0x14(int)
		AnnotationCmd:89 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Return","stmt":{"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":28,"charByteOffset":4},"end":{"line":28,"charByteOffset":15}},"exps":[{"#class":"spec.cvlast.CVLExp.VariableExp","id":"ret","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":28,"charByteOffset":11},"end":{"line":28,"charByteOffset":14}}},"twoStateIndex":"NEITHER"}],"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.CVLRet.PrimitiveRet","callIndex":1,"index":0,"sym":{"namePrefix":"I23","tag":{"#class":"tac.Tag.Int"},"callIndex":0},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"label":{"stmt":{"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":28,"charByteOffset":4},"end":{"line":28,"charByteOffset":15}},"exps":[{"#class":"spec.cvlast.CVLExp.VariableExp","id":"ret","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":28,"charByteOffset":11},"end":{"line":28,"charByteOffset":14}}},"twoStateIndex":"NEITHER"}],"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":4}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}}
		AssignExpCmd:76 CANON22:34 0x14(int)
		AnnotationCmd:76 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":25}
		AnnotationCmd:76 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.CVLFunctionEnd","callIndex":1,"name":"func"}}
		AnnotationCmd:76 JSON{"key":{"name":"revert.confluence","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}
		LabelCmd:76 "join point of revert handling"
	}
	Block 2_0_0_0_0_0 Succ [3_0_0_2_0_0] {
		AnnotationCmd:76 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":21}
		AnnotationCmd:90 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Definition","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":36,"charByteOffset":4},"end":{"line":36,"charByteOffset":30}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"idL":[{"#class":"spec.cvlast.CVLLhs.Id","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":36,"charByteOffset":4},"end":{"line":36,"charByteOffset":14}},"id":"r2","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":36,"charByteOffset":4},"end":{"line":36,"charByteOffset":14}}}}],"exp":{"#class":"spec.cvlast.CVLExp.ApplyExp.ContractFunction.Concrete","methodIdWithCallContext":{"#class":"spec.cvlast.ConcreteMethod","signature":{"#class":"spec.cvlast.ExternalQualifiedMethodSignature.ExternalQualifiedMethodSig","wrapped":{"#class":"spec.cvlast.QualifiedMethodSignature.QualifiedMethodSig","qualifiedMethodName":{"#class":"spec.cvlast.QualifiedFunction","host":{"name":"TestContract"},"methodId":"add"},"params":[{"#class":"spec.cvlast.VMParam.Named","name":"a","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}},{"#class":"spec.cvlast.VMParam.Named","name":"b","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}}],"res":[{"#class":"spec.cvlast.VMParam.Unnamed","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}}]},"sighashInt":{"n":"771602f7"}}},"args":[{"#class":"spec.cvlast.CVLExp.VariableExp","id":"e","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":36,"charByteOffset":21},"end":{"line":36,"charByteOffset":22}}},"twoStateIndex":"NEITHER"},{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"4","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"4"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":36,"charByteOffset":24},"end":{"line":36,"charByteOffset":25}}}},{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"5","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"5"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":36,"charByteOffset":27},"end":{"line":36,"charByteOffset":28}}}}],"noRevert":true,"storage":{"id":"lastStorage","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.VMInternal.BlockchainState"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Empty","comment":"empty storage type"}},"twoStateIndex":"NEITHER"},"isWhole":false,"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.ReturnValue"}},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":36,"charByteOffset":17},"end":{"line":36,"charByteOffset":29}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.CallResolution$DirectPassing","target":{"methodSignature":{"#class":"spec.cvlast.ExternalQualifiedMethodSignature.ExternalQualifiedMethodSig","wrapped":{"#class":"spec.cvlast.QualifiedMethodSignature.QualifiedMethodSig","qualifiedMethodName":{"#class":"spec.cvlast.QualifiedFunction","host":{"name":"TestContract"},"methodId":"add"},"params":[{"#class":"spec.cvlast.VMParam.Named","name":"a","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}},{"#class":"spec.cvlast.VMParam.Named","name":"b","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}}],"res":[{"#class":"spec.cvlast.VMParam.Unnamed","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}}]},"sighashInt":{"n":"771602f7"}},"definitelyNonPayable":true,"annotation":{"visibility":"EXTERNAL","envFree":false,"library":false,"virtual":false},"stateMutability":"nonpayable","evmExternalMethodInfo":{"sigHash":"771602f7","name":"add","argTypes":[{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256},{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}],"resultTypes":[{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}],"stateMutability":"nonpayable","isConstant":false,"paramNames":["a","b"],"isLibrary":false,"contractName":"TestContract","contractInstanceId":"ce4604a0000000000000000000000001","sourceSegment":{"range":{"specFile":"TestContract.sol","start":{"line":5,"charByteOffset":4},"end":{"line":7,"charByteOffset":5}},"content":"function add(uint256 a, uint256 b) public returns (uint256) {\n        return a + b;\n    }"}}},"hasEnv":true}}},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AnnotationCmd JSON{"key":{"name":"cvl.trace.data.movement","type":"spec.CVLCompiler$Companion$TraceMeta$CVLMovement","erasureStrategy":"Erased"},"value":{"dst":{"id":"certoraArg246247"},"src":{"id":"e230"}}}
		AssignExpCmd:91 I25 0x4
		AssignExpCmd:92 I26 0x5
	}
	Block 3_0_0_2_0_0 Succ [4_0_0_3_0_2] {
		AssignHavocCmd:93 CANON26!!27:35
		AnnotationCmd:93 JSON{"key":{"name":"call.trace.push","type":"analysis.icfg.Inliner$CallStack$PushRecord","erasureStrategy":"Canonical"},"value":{"callee":{"contractId":"ce4604a0000000000000000000000001","sigHash":{"n":"771602f7"},"attr":{"#class":"scene.MethodAttribute.Common"}},"summary":null,"convention":{"#class":"analysis.icfg.Inliner.CallConventionType.FromCVL"},"calleeId":2}}
		AssignHavocCmd:93 tacCalldatasize!!28:9
		AssumeExpCmd Eq(tacCalldatasize!!28:9 0x44 )
		AssignExpCmd:93 tacCalldatabuf@2:14 MapDefinition(CANON27:bv256 -> Ite(Lt(CANON27 tacCalldatasize!!28:9 ) Select(Select(Select(CANON28!7:25 CANON27 ) tacCalldatasize!!28:9 ) 0x771602f7 ) 0x0 ) bytemap)
		AssignExpCmd:93 R29:20 Select(Select(Select(CANON28!7:25 0x0 ) 0x44 ) 0x771602f7 )
		AssumeExpCmd LAnd(Ge(R29:20 0x771602f700000000000000000000000000000000000000000000000000000000 ) Le(R29:20 0x771602f7ffffffffffffffffffffffffffffffffffffffffffffffffffffffff ) )
		AnnotationCmd:93 JSON{"key":{"name":"cvl.arg-serialization.start","type":"spec.CVLInvocationCompiler$StartSerializationMarker","erasureStrategy":"Canonical"},"value":{"id":0,"callId":2}}
		LabelCmd:93 "1: Read primitive from certoraArg248249:int..."
		AssertCmd:94 true "sanity bounds check on cvl to vm encoding (unsigned int elements of a user array) of %1$s failed"
		AssertCmd:94 true "sanity bounds check on cvl to vm encoding (unsigned int elements of a user array) of %1$s failed"
		AssignExpCmd:93 tacCalldatabufCANON0@2:2 0x4
		LabelCmd:93 "...done 1"
		AnnotationCmd JSON{"key":{"name":"cvl.trace.external","type":"spec.CVLCompiler$Companion$TraceMeta$ExternalArg","erasureStrategy":"Erased"},"value":{"s":{"#class":"spec.CVLCompiler.Companion.TraceMeta.ValueIdentity.TACVar","t":{"namePrefix":"I25","tag":{"#class":"tac.Tag.Int"},"callIndex":0}},"rootOffset":"0","callId":2,"targetType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"sourceType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"4"},"fields":null}}
		LabelCmd:93 "2: Read primitive from certoraArg250251:int..."
		AssertCmd:95 true "sanity bounds check on cvl to vm encoding (unsigned int elements of a user array) of %1$s failed"
		AssertCmd:95 true "sanity bounds check on cvl to vm encoding (unsigned int elements of a user array) of %1$s failed"
		AssignExpCmd:93 tacCalldatabufCANON1@2:3 0x5
		LabelCmd:93 "...done 2"
		AnnotationCmd JSON{"key":{"name":"cvl.trace.external","type":"spec.CVLCompiler$Companion$TraceMeta$ExternalArg","erasureStrategy":"Erased"},"value":{"s":{"#class":"spec.CVLCompiler.Companion.TraceMeta.ValueIdentity.TACVar","t":{"namePrefix":"I26","tag":{"#class":"tac.Tag.Int"},"callIndex":0}},"rootOffset":"20","callId":2,"targetType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"sourceType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"5"},"fields":null}}
		AnnotationCmd:93 JSON{"key":{"name":"cvl.arg-serialization.end","type":"spec.CVLInvocationCompiler$EndSerializationMarker","erasureStrategy":"Canonical"},"value":{"id":0,"callId":2}}
		AssignExpCmd:93 lastHasThrown!!30:42 false
		AssertCmd:96 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:97 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:98 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:99 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:100 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:101 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:102 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:103 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:104 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:105 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:106 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:107 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssignExpCmd:93 R32:20 Apply(safe_math_narrow_bv256:bif CANON4:43)
		AssignExpCmd:93 R34:20 Select(tacBalance!!5:13 Apply(to_skey:bif R32:20) )
		AssignExpCmd:108 tacBalance!!36:13 Store(tacBalance!!5:13 Apply(to_skey:bif R32:20) R34:20 )
		AssignExpCmd:93 R37:20 Select(tacBalance!!36:13 Apply(to_skey:bif R12:23) )
		AssignExpCmd:108 R39:20 Apply(safe_math_narrow_bv256:bif R37:20)
		AssignExpCmd:108 tacBalance!!40:13 Store(tacBalance!!36:13 Apply(to_skey:bif R12:23) R39:20 )
		AnnotationCmd:93 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.TransferSnippet","srcAccountInfo":{"old":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R34","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"new":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R34","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"addr":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R32","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]}},"trgAccountInfo":{"old":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R37","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"new":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R39","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"addr":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R12","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry","name":"tacContractAt"}},{"key":{"name":"tac.contract.sym.addr.name","type":"java.lang.String","erasureStrategy":"Erased"},"value":"TestContract"},{"key":{"name":"tac.contract.sym.addr","type":"java.math.BigInteger","erasureStrategy":"Erased"},"value":"ce4604a0000000000000000000000001"}]}},"transferredAmount":{"#class":"vc.data.TACSymbol.Const","value":"0"}}}
		LabelCmd:93 "Start procedure TestContract-add(uint256,uint256)"
		AnnotationCmd:93 JSON{"key":{"name":"fps.free-pointer-is-scalarized","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true}
		AssignExpCmd:93 R41:20 Select(tacExtcodesize!!4:7 Apply(to_skey:bif R12:109) )
		AssumeExpCmd Ge(R41:20 0x1 )
		AnnotationCmd:93 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.RawStorageAccess.WithLocSym","isLoad":true,"loc":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R12","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"tacAddress","maybeTACKeywordOrdinal":22}},{"key":{"name":"tac.env.known-bit-width","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":160},{"key":{"name":"tac.contract.sym.addr.name","type":"java.lang.String","erasureStrategy":"Erased"},"value":"TestContract"},{"key":{"name":"tac.contract.sym.addr","type":"java.math.BigInteger","erasureStrategy":"Erased"},"value":"ce4604a0000000000000000000000001"}]},"contractInstance":"ce4604a0000000000000000000000001","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R41","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"storageType":null,"range":null}}
		AnnotationCmd:93 JSON{"key":{"name":"internal.func.finder.info","type":"analysis.ip.InternalFunctionFinderReport","erasureStrategy":"Erased"},"value":{"unresolvedFunctions":[]}}
		AnnotationCmd:93 JSON{"key":{"name":"fps.free-pointer-is-scalarized","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":0,"bytecodeCount":8,"sources":[{"source":0,"begin":25,"end":2021}]}}
		LabelCmd "→ Assuming FP is strictly monotonic increasing"
		LabelCmd "←"
		AnnotationCmd:93 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.StartBranchSnippet","branchIndex":0,"branchSource":{"range":{"specFile":"TestContract.sol","start":{"line":2,"charByteOffset":0},"end":{"line":24,"charByteOffset":1}},"content":"contract TestContract {...}"}}}
		AnnotationCmd:93 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.EndBranchSnippet","branchIndex":0}}
		AnnotationCmd:110 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":16,"bytecodeCount":7,"sources":[{"source":0,"begin":25,"end":2021}]}}
		AnnotationCmd:110 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":26,"bytecodeCount":9,"sources":[{"source":0,"begin":25,"end":2021}]}}
		AnnotationCmd:110 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":43,"bytecodeCount":5,"sources":[{"source":0,"begin":25,"end":2021}]}}
		AnnotationCmd:110 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":54,"bytecodeCount":5,"sources":[{"source":0,"begin":25,"end":2021}]}}
		AnnotationCmd:110 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":150,"bytecodeCount":14,"sources":[{"source":0,"begin":75,"end":500}]}}
		AnnotationCmd:111 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1105,"bytecodeCount":11,"sources":[{"source":1,"begin":420,"end":827},{"source":1,"begin":488,"end":494},{"source":1,"begin":496,"end":502},{"source":1,"begin":545,"end":547},{"source":1,"begin":533,"end":542},{"source":1,"begin":524,"end":531},{"source":1,"begin":520,"end":543},{"source":1,"begin":516,"end":548},{"source":1,"begin":513,"end":515}]}}
		AnnotationCmd:93 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.StartBranchSnippet","branchIndex":1,"branchSource":{"range":{"specFile":"TestContract.sol","start":{"line":5,"charByteOffset":4},"end":{"line":7,"charByteOffset":5}},"content":"compiler-generate condition in function add(uint256 a, uint256 b) public returns (uint256) "}}}
		AnnotationCmd:93 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.EndBranchSnippet","branchIndex":1}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1124,"bytecodeCount":9,"sources":[{"source":1,"begin":513,"end":515},{"source":1,"begin":604,"end":605},{"source":1,"begin":629,"end":682},{"source":1,"begin":674,"end":681},{"source":1,"begin":665,"end":671},{"source":1,"begin":654,"end":663},{"source":1,"begin":650,"end":672}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1043,"bytecodeCount":10,"sources":[{"source":1,"begin":7,"end":146},{"source":1,"begin":53,"end":58},{"source":1,"begin":91,"end":97},{"source":1,"begin":78,"end":98},{"source":1,"begin":69,"end":98},{"source":1,"begin":107,"end":140},{"source":1,"begin":134,"end":139}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1440,"bytecodeCount":5,"sources":[{"source":1,"begin":2119,"end":2241},{"source":1,"begin":2192,"end":2216},{"source":1,"begin":2210,"end":2215}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1383,"bytecodeCount":9,"sources":[{"source":1,"begin":1850,"end":1927},{"source":1,"begin":1887,"end":1894},{"source":1,"begin":1916,"end":1921},{"source":1,"begin":1905,"end":1921},{"source":1,"begin":1895,"end":1927}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1449,"bytecodeCount":5,"sources":[{"source":1,"begin":2192,"end":2216},{"source":1,"begin":2185,"end":2190},{"source":1,"begin":2182,"end":2217},{"source":1,"begin":2172,"end":2174}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1460,"bytecodeCount":3,"sources":[{"source":1,"begin":2172,"end":2174},{"source":1,"begin":2162,"end":2241}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1058,"bytecodeCount":6,"sources":[{"source":1,"begin":107,"end":140},{"source":1,"begin":59,"end":146}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1138,"bytecodeCount":12,"sources":[{"source":1,"begin":629,"end":682},{"source":1,"begin":619,"end":682},{"source":1,"begin":575,"end":692},{"source":1,"begin":731,"end":733},{"source":1,"begin":757,"end":810},{"source":1,"begin":802,"end":809},{"source":1,"begin":793,"end":799},{"source":1,"begin":782,"end":791},{"source":1,"begin":778,"end":800}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1043,"bytecodeCount":10,"sources":[{"source":1,"begin":7,"end":146},{"source":1,"begin":53,"end":58},{"source":1,"begin":91,"end":97},{"source":1,"begin":78,"end":98},{"source":1,"begin":69,"end":98},{"source":1,"begin":107,"end":140},{"source":1,"begin":134,"end":139}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1440,"bytecodeCount":5,"sources":[{"source":1,"begin":2119,"end":2241},{"source":1,"begin":2192,"end":2216},{"source":1,"begin":2210,"end":2215}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1383,"bytecodeCount":9,"sources":[{"source":1,"begin":1850,"end":1927},{"source":1,"begin":1887,"end":1894},{"source":1,"begin":1916,"end":1921},{"source":1,"begin":1905,"end":1921},{"source":1,"begin":1895,"end":1927}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1449,"bytecodeCount":5,"sources":[{"source":1,"begin":2192,"end":2216},{"source":1,"begin":2185,"end":2190},{"source":1,"begin":2182,"end":2217},{"source":1,"begin":2172,"end":2174}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1460,"bytecodeCount":3,"sources":[{"source":1,"begin":2172,"end":2174},{"source":1,"begin":2162,"end":2241}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1058,"bytecodeCount":6,"sources":[{"source":1,"begin":107,"end":140},{"source":1,"begin":59,"end":146}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1155,"bytecodeCount":10,"sources":[{"source":1,"begin":757,"end":810},{"source":1,"begin":747,"end":810},{"source":1,"begin":702,"end":820},{"source":1,"begin":503,"end":827}]}}
		AnnotationCmd:93 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":171,"bytecodeCount":3,"sources":[{"source":0,"begin":75,"end":500}]}}
		JumpCmd 4_0_0_3_0_2
	}
	Block 4_0_0_3_0_2 Succ [5_0_0_2_0_0] {
		AnnotationCmd JSON{"key":{"name":"call.trace.internal.summary.start","type":"analysis.icfg.SummaryStack$SummaryStart$Internal","erasureStrategy":"CallTrace"},"value":"rO0ABXNyADBhbmFseXNpcy5pY2ZnLlN1bW1hcnlTdGFjayRTdW1tYXJ5U3RhcnQkSW50ZXJuYWze2wAmittJZwIABUwADmFwcGxpZWRTdW1tYXJ5dAAsTGFuYWx5c2lzL2ljZmcvU3VtbWFyaXphdGlvbiRBcHBsaWVkU3VtbWFyeTtMABdjYWxsUmVzb2x1dGlvblRhYmxlSW5mb3QANkxyZXBvcnQvY2FsbHJlc29sdXRpb24vQ2FsbFJlc29sdXRpb25UYWJsZVN1bW1hcnlJbmZvO0wAC2NhbGxTaXRlU3JjdAAVTHZjL2RhdGEvVEFDTWV0YUluZm87TAAPbWV0aG9kU2lnbmF0dXJldAAmTHNwZWMvY3ZsYXN0L1F1YWxpZmllZE1ldGhvZFNpZ25hdHVyZTtMAAdzdXBwb3J0dAAPTGphdmEvdXRpbC9TZXQ7eHIAJ2FuYWx5c2lzLmljZmcuU3VtbWFyeVN0YWNrJFN1bW1hcnlTdGFydM6P29O9R0c9AgAAeHBzcgA3YW5hbHlzaXMuaWNmZy5TdW1tYXJpemF0aW9uJEFwcGxpZWRTdW1tYXJ5JE1ldGhvZHNCbG9ja8QZaUG9nkK8AgACTAAMc3BlY0NhbGxTdW1tdAAuTHNwZWMvY3ZsYXN0L1NwZWNDYWxsU3VtbWFyeSRFeHByZXNzaWJsZUluQ1ZMO0wAEHN1bW1hcml6ZWRNZXRob2R0ABtMc3BlYy9DVkwkU3VtbWFyeVNpZ25hdHVyZTt4cHNyAB9zcGVjLmN2bGFzdC5TcGVjQ2FsbFN1bW1hcnkkRXhwBa/ML1lm2f4CAAdMAAhjdmxSYW5nZXQAFkxzcGVjL2N2bGFzdC9DVkxSYW5nZTtMAANleHB0ABRMc3BlYy9jdmxhc3QvQ1ZMRXhwO0wADGV4cGVjdGVkVHlwZXQAEExqYXZhL3V0aWwvTGlzdDtMAAlmdW5QYXJhbXNxAH4AD0wABXNjb3BldAAWTHNwZWMvY3ZsYXN0L0NWTFNjb3BlO0wAEXN1bW1hcml6YXRpb25Nb2RldAAvTHNwZWMvY3ZsYXN0L1NwZWNDYWxsU3VtbWFyeSRTdW1tYXJpemF0aW9uTW9kZTtMAAp3aXRoQ2xhdXNldAAsTHNwZWMvY3ZsYXN0L1NwZWNDYWxsU3VtbWFyeSRFeHAkV2l0aENsYXVzZTt4cgAsc3BlYy5jdmxhc3QuU3BlY0NhbGxTdW1tYXJ5JEV4cHJlc3NpYmxlSW5DVkwEHG3pUuDAOwIAAHhyABtzcGVjLmN2bGFzdC5TcGVjQ2FsbFN1bW1hcnmf4QieXcWlAQIAAHhwc3IAGnNwZWMuY3ZsYXN0LkNWTFJhbmdlJFJhbmdlpjwN4KUDjBsCAANMAANlbmR0ABZMdXRpbHMvU291cmNlUG9zaXRpb247TAAIc3BlY0ZpbGV0ABJMamF2YS9sYW5nL1N0cmluZztMAAVzdGFydHEAfgAXeHIAFHNwZWMuY3ZsYXN0LkNWTFJhbmdlGs0T2CQ+QuYCAAB4cHNyABR1dGlscy5Tb3VyY2VQb3NpdGlvbpX059TqmcSNAgACSQAOY2hhckJ5dGVPZmZzZXRJAARsaW5leHAAAABfAAAAAXQACkJhc2ljLnNwZWNzcQB+ABsAAABSAAAAAXNyACdzcGVjLmN2bGFzdC5DVkxFeHAkQXBwbHlFeHAkQ1ZMRnVuY3Rpb24IX/LH9tAwOgIABVoACG5vUmV2ZXJ0TAAEYXJnc3EAfgAPTAACaWRxAH4AGEwAF21ldGhvZElkV2l0aENhbGxDb250ZXh0dAAdTHNwZWMvY3ZsYXN0L1NwZWNEZWNsYXJhdGlvbjtMAAN0YWd0ABdMc3BlYy9jdmxhc3QvQ1ZMRXhwVGFnO3hyABtzcGVjLmN2bGFzdC5DVkxFeHAkQXBwbHlFeHAF3JlNR+1SuwIAAHhyACFzcGVjLmN2bGFzdC5DVkxFeHAkQXBwbGljYXRpb25FeHAEe7zFegP5fQIAAHhyABJzcGVjLmN2bGFzdC5DVkxFeHCM/spMMCiwgAIAAHhwAXNyABNqYXZhLnV0aWwuQXJyYXlMaXN0eIHSHZnHYZ0DAAFJAARzaXpleHAAAAACdwQAAAACc3IAHnNwZWMuY3ZsYXN0LkNWTEV4cCRWYXJpYWJsZUV4cJ0ULkp52IKNAgAETAACaWRxAH4AGEwADG9yaWdpbmFsTmFtZXEAfgAYTAADdGFncQB+ACFMAA10d29TdGF0ZUluZGV4dAAbTHNwZWMvY3ZsYXN0L1R3b1N0YXRlSW5kZXg7eHEAfgAkdAABYXEAfgArc3IAFXNwZWMuY3ZsYXN0LkNWTEV4cFRhZw3AM9oKBCcAAgAFWgAJaGFzUGFyZW5zTAAKYW5ub3RhdGlvbnQAIkxzcGVjL2N2bGFzdC9FeHByZXNzaW9uQW5ub3RhdGlvbjtMAAhjdmxSYW5nZXEAfgANTAAFc2NvcGVxAH4AEEwABHR5cGV0ABVMc3BlYy9jdmxhc3QvQ1ZMVHlwZTt4cABwc3EAfgAWc3EAfgAbAAAAWwAAAAFxAH4AHXNxAH4AGwAAAFoAAAABc3IAFHNwZWMuY3ZsYXN0LkNWTFNjb3BlIslgWNQdXVQCAANMABZoYXNoQ29kZUNhY2hlJGRlbGVnYXRldAANTGtvdGxpbi9MYXp5O0wACmlubmVyU2NvcGVxAH4AEEwACnNjb3BlU3RhY2txAH4AD3hwc3IAGmtvdGxpbi5Jbml0aWFsaXplZExhenlJbXBse8d/8SAqgY0CAAFMAAV2YWx1ZXQAEkxqYXZhL2xhbmcvT2JqZWN0O3hwc3IAEWphdmEubGFuZy5JbnRlZ2VyEuKgpPeBhzgCAAFJAAV2YWx1ZXhyABBqYXZhLmxhbmcuTnVtYmVyhqyVHQuU4IsCAAB4cMzxqF9zcQB+ADNzcQB+ADZzcQB+ADlOZ41hc3EAfgAzc3EAfgA2c3EAfgA5AAAAH3BzcgAca290bGluLmNvbGxlY3Rpb25zLkVtcHR5TGlzdJlvx9Cn4GAyAgAAeHBzcgAjamF2YS51dGlsLkNvbGxlY3Rpb25zJFNpbmdsZXRvbkxpc3Qq7ykQPKeblwIAAUwAB2VsZW1lbnRxAH4AN3hwc3IAJnNwZWMuY3ZsYXN0LkNWTFNjb3BlJEl0ZW0kQXN0U2NvcGVJdGVth5un9wbVoZMCAAB4cgAZc3BlYy5jdmxhc3QuQ1ZMU2NvcGUkSXRlbS8Dr/+eN1ZFAgAAeHBzcQB+ACYAAAACdwQAAAACcQB+AEhzcgArc3BlYy5jdmxhc3QuQ1ZMU2NvcGUkSXRlbSRFeHByZXNzaW9uU3VtbWFyeQ8zGp1aX6loAgABSQAHc2NvcGVJZHhyAClzcGVjLmN2bGFzdC5DVkxTY29wZSRJdGVtJEFTVEVsZW1lbnRTY29wZVKrjxFR5CKWAgABTAAHZWxlbWVudHQAGkxzcGVjL2N2bGFzdC9DcmVhdGVzU2NvcGU7eHEAfgBHc3EAfgAMcQB+ABpzcgAlc3BlYy5jdmxhc3QuQ1ZMRXhwJFVucmVzb2x2ZWRBcHBseUV4cDU+F4IbuX3IAgAIWgAMaW52b2tlSXNTYWZlWgANaW52b2tlSXNXaG9sZUwABGFyZ3NxAH4AD0wABGJhc2VxAH4ADkwADWludm9rZVN0b3JhZ2V0ACBMc3BlYy9jdmxhc3QvQ1ZMRXhwJFZhcmlhYmxlRXhwO0wACG1ldGhvZElkcQB+ABhMAAN0YWdxAH4AIUwADXR3b1N0YXRlSW5kZXhxAH4AKXhxAH4AIwEAc3EAfgAmAAAAAncEAAAAAnNxAH4AKHEAfgArcQB+ACtzcQB+ACwAcHEAfgAwcQB+ADVwfnIAGXNwZWMuY3ZsYXN0LlR3b1N0YXRlSW5kZXgAAAAAAAAAABIAAHhyAA5qYXZhLmxhbmcuRW51bQAAAAAAAAAAEgAAeHB0AAdORUlUSEVSc3EAfgAodAABYnEAfgBac3EAfgAsAHBzcQB+ABZzcQB+ABsAAABeAAAAAXEAfgAdc3EAfgAbAAAAXQAAAAFxAH4ANXBxAH4AV3hwc3EAfgAodAALbGFzdFN0b3JhZ2VxAH4AYHNxAH4ALABwc3IAGnNwZWMuY3ZsYXN0LkNWTFJhbmdlJEVtcHR5CkFC2rDl068CAAFMAAdjb21tZW50cQB+ABh4cQB+ABl0ABJlbXB0eSBzdG9yYWdlIHR5cGVxAH4ANXBxAH4AV3QAB2N2bF9hZGRzcQB+ACwAcHNxAH4AFnNxAH4AGwAAAF8AAAABcQB+AB1zcQB+ABsAAABSAAAAAXEAfgA1cHEAfgBXcHNxAH4AJgAAAAJ3BAAAAAJzcgAZc3BlYy5jdmxhc3QuVk1QYXJhbSROYW1lZP0Lrr551hlsAgAETAAEbmFtZXEAfgAYTAAMb3JpZ2luYWxOYW1lcQB+ABhMAAVyYW5nZXEAfgANTAAGdm1UeXBldAAuTHNwZWMvY3ZsYXN0L3R5cGVkZXNjcmlwdG9ycy9WTVR5cGVEZXNjcmlwdG9yO3hyABNzcGVjLmN2bGFzdC5WTVBhcmFtfI1Mdm6wsYgCAAB4cHEAfgArcQB+ACtzcQB+ABZzcQB+ABsAAAAnAAAAAXEAfgAdc3EAfgAbAAAAHgAAAAFzcgAzc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkVWTVR5cGVEZXNjcmlwdG9yJFVJbnRLqHosSzB6DiUCAAFJAAhiaXR3aWR0aHhyAERzcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRVZNVHlwZURlc2NyaXB0b3IkRVZNSXNvbW9ycGhpY1ZhbHVlVHlwZZbjlXdq3fF/AgAAeHIAOnNwZWMuY3ZsYXN0LnR5cGVkZXNjcmlwdG9ycy5FVk1UeXBlRGVzY3JpcHRvciRFVk1WYWx1ZVR5cGUQ5NL1qK834QIAAHhyAC1zcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRVZNVHlwZURlc2NyaXB0b3JeVh3cxo4+6AIAAHhwAAABAHNxAH4Aa3EAfgBacQB+AFpzcQB+ABZzcQB+ABsAAAAyAAAAAXEAfgAdc3EAfgAbAAAAKQAAAAFzcQB+AHIAAAEAeHEAfgA1fnIALXNwZWMuY3ZsYXN0LlNwZWNDYWxsU3VtbWFyeSRTdW1tYXJpemF0aW9uTW9kZQAAAAAAAAAAEgAAeHEAfgBWdAADQUxMcAAAAAB4c3IAFnNwZWMuY3ZsYXN0LkNWTFR5cGUkVk2jqzstHXzffQIAAkwAB2NvbnRleHR0ACtMc3BlYy9jdmxhc3QvdHlwZWRlc2NyaXB0b3JzL0Zyb21WTUNvbnRleHQ7TAAKZGVzY3JpcHRvcnEAfgBseHIAE3NwZWMuY3ZsYXN0LkNWTFR5cGV0MROVt8FlUAIAAHhwc3IAQ3NwZWMuY3ZsYXN0LnR5cGVkZXNjcmlwdG9ycy5Gcm9tVk1Db250ZXh0JEludGVybmFsU3VtbWFyeUFyZ0JpbmRpbmeexeTPAT+JJwIAAHhyAClzcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRnJvbVZNQ29udGV4dMXa8Yb3d/BlAgAAeHBxAH4AdnEAfgBXc3EAfgAocQB+AFpxAH4AWnNxAH4ALABwcQB+AFxxAH4ANXNxAH4Af3EAfgCFcQB+AHtxAH4AV3hxAH4AZXNyABtzcGVjLmN2bGFzdC5TcGVjRGVjbGFyYXRpb26NFvQPPKihtwIAAUwACG1ldGhvZElkcQB+ABh4cHEAfgBlc3EAfgAsAHNyABdzcGVjLmN2bGFzdC5DVkxGdW5jdGlvbku8gkthesgEAgAJTAAFYmxvY2txAH4AD0wACGN2bFJhbmdlcQB+AA1MAA1kZWNsYXJhdGlvbklkcQB+ABhMABJmdW5jdGlvbklkZW50aWZpZXJxAH4AIEwACnBhcmFtVHlwZXNxAH4AD0wABnBhcmFtc3EAfgAPTAAEcmV0c3QAIUxzcGVjL2N2bGFzdC9DVkxUeXBlJFB1cmVDVkxUeXBlO0wABXNjb3BlcQB+ABBMAA90eXBlRGVzY3JpcHRpb25xAH4AGHhwc3EAfgAmAAAAAXcEAAAAAXNyACBzcGVjLmN2bGFzdC5DVkxDbWQkU2ltcGxlJFJldHVybtK6rd+vqZLkAgAETAAHY21kTmFtZXEAfgAYTAAIY3ZsUmFuZ2VxAH4ADUwABGV4cHNxAH4AD0wABXNjb3BlcQB+ABB4cgAZc3BlYy5jdmxhc3QuQ1ZMQ21kJFNpbXBsZYD/kUsK5pNIAgAAeHIAEnNwZWMuY3ZsYXN0LkNWTENtZPmgwiQ8K8feAgAAeHB0AAZyZXR1cm5zcQB+ABZzcQB+ABsAAAAiAAAADHEAfgAdc3EAfgAbAAAABAAAAAxzcQB+ACYAAAABdwQAAAABc3IAG3NwZWMuY3ZsYXN0LkNWTEV4cCRDYXN0RXhwchbId48fbNyfAgAFTAADYXJncQB+AA5MAAhjYXN0VHlwZXQAD0xzcGVjL0Nhc3RUeXBlO0wADGluQ1ZMQmxvY2tJZHQAE0xqYXZhL2xhbmcvSW50ZWdlcjtMAAN0YWdxAH4AIUwACnRvQ2FzdFR5cGVxAH4AjXhxAH4AJHNyACNzcGVjLmN2bGFzdC5DVkxFeHAkQmluYXJ5RXhwJEFkZEV4cMkd16VHB6Z9AgADTAABbHEAfgAOTAABcnEAfgAOTAADdGFncQB+ACF4cgAcc3BlYy5jdmxhc3QuQ1ZMRXhwJEJpbmFyeUV4cJIRn4AfygEmAgAAeHEAfgAkc3EAfgAocQB+ACtxAH4AK3NxAH4ALABwc3EAfgAWc3EAfgAbAAAAHAAAAAxxAH4AHXNxAH4AGwAAABsAAAAMc3EAfgAzc3EAfgA2c3EAfgA5zPGovHEAfgA8c3EAfgAmAAAAAncEAAAAAnEAfgBIc3IALnNwZWMuY3ZsYXN0LkNWTFNjb3BlJEl0ZW0kQ1ZMRnVuY3Rpb25TY29wZUl0ZW17W8hAYYNKOQIAAUkAB3Njb3BlSWR4cQB+AEtzcQB+AIxzcQB+ACYAAAABdwQAAAABc3EAfgCQcQB+AJRxAH4AlXNxAH4AJgAAAAF3BAAAAAFzcQB+AJlzcQB+AJ1zcQB+AChxAH4AK3EAfgArcQB+AKFxAH4AV3NxAH4AKHEAfgBacQB+AFpzcQB+ACwAcHNxAH4AFnNxAH4AGwAAACAAAAAMcQB+AB1zcQB+ABsAAAAfAAAADHEAfgClcHEAfgBXc3EAfgAsAHBzcQB+ABZzcQB+ABsAAAAgAAAADHEAfgAdc3EAfgAbAAAAGwAAAAxxAH4ApXB+cgANc3BlYy5DYXN0VHlwZQAAAAAAAAAAEgAAeHEAfgBWdAAHUkVRVUlSRXBzcQB+ACwAcHNxAH4AFnNxAH4AGwAAACAAAAAMcQB+AB1zcQB+ABsAAAALAAAADHEAfgClcHNyAC9zcGVjLmN2bGFzdC5DVkxUeXBlJFB1cmVDVkxUeXBlJFByaW1pdGl2ZSRVSW50S7kLmo4pEkYpAgACSQAIYml0V2lkdGhJAAFreHIAKXNwZWMuY3ZsYXN0LkNWTFR5cGUkUHVyZUNWTFR5cGUkUHJpbWl0aXZlCpvb/zR+wjsCAAB4cgAfc3BlYy5jdmxhc3QuQ1ZMVHlwZSRQdXJlQ1ZMVHlwZf0GtBZTtiixAgAAeHEAfgCBAAABAAAAAQB4cQB+AKV4c3EAfgAWc3EAfgAbAAAAAQAAAA1xAH4AHXNxAH4AGwAAAAAAAAALcQB+AGVzcQB+AIlxAH4AZXNxAH4AJgAAAAJ3BAAAAAJzcQB+AMIAAAEAAAABAHNxAH4AwgAAAQAAAAEAeHNxAH4AJgAAAAJ3BAAAAAJzcgAUc3BlYy5jdmxhc3QuQ1ZMUGFyYW1RTQ5pEi1lHgIABEwAAmlkcQB+ABhMAApvcmlnaW5hbElkcQB+ABhMAAVyYW5nZXEAfgANTAAEdHlwZXEAfgCNeHBxAH4AK3EAfgArc3EAfgAWc3EAfgAbAAAAGgAAAAtxAH4AHXNxAH4AGwAAABEAAAALcQB+AMtzcQB+AM5xAH4AWnEAfgBac3EAfgAWc3EAfgAbAAAAJQAAAAtxAH4AHXNxAH4AGwAAABwAAAALcQB+AMx4c3EAfgDCAAABAAAAAQBxAH4ApXQADENWTCBmdW5jdGlvbgAAAAN4cHEAfgBXc3EAfgAocQB+AFpxAH4AWnEAfgCzcQB+AFdxAH4At3EAfgC8cHEAfgC+cQB+AMV4cQB+AKV4cQB+AMZxAH4AZXNxAH4AiXEAfgBlc3EAfgAmAAAAAncEAAAAAnEAfgDLcQB+AMx4c3EAfgAmAAAAAncEAAAAAnEAfgDPcQB+ANN4cQB+ANdxAH4ApXEAfgDYcQB+AGdxAH4ANXEAfgDXcHNxAH4AJgAAAAJ3BAAAAAJxAH4AbnEAfgB3eHEAfgA1cQB+AH1wc3IAFnNwZWMuQ1ZMJEludGVybmFsRXhhY3SF/Egh8I7sYAIAAUwACXNpZ25hdHVyZXQAL0xzcGVjL2N2bGFzdC9RdWFsaWZpZWRNZXRob2RQYXJhbWV0ZXJTaWduYXR1cmU7eHBzcgA3c3BlYy5jdmxhc3QuUXVhbGlmaWVkTWV0aG9kU2lnbmF0dXJlJFF1YWxpZmllZE1ldGhvZFNpZxh9TLRtHWz1AgADTAAGcGFyYW1zcQB+AA9MABNxdWFsaWZpZWRNZXRob2ROYW1ldAAoTHNwZWMvY3ZsYXN0L0NvbnRyYWN0RnVuY3Rpb25JZGVudGlmaWVyO0wAA3Jlc3EAfgAPeHBxAH4AanNyAB1zcGVjLmN2bGFzdC5RdWFsaWZpZWRGdW5jdGlvbuUpTPLkOVGDAgACTAAEaG9zdHQAHkxzcGVjL2N2bGFzdC9Tb2xpZGl0eUNvbnRyYWN0O0wACG1ldGhvZElkcQB+ABh4cHNyABxzcGVjLmN2bGFzdC5Tb2xpZGl0eUNvbnRyYWN0I2l9dxqBPaICAAFMAARuYW1lcQB+ABh4cHQADFRlc3RDb250cmFjdHQAA2FkZHNxAH4AJgAAAAF3BAAAAAFzcgAbc3BlYy5jdmxhc3QuVk1QYXJhbSRVbm5hbWVkAg9NufzldWUCAAJMAAVyYW5nZXEAfgANTAAGdm1UeXBlcQB+AGx4cQB+AG1zcQB+ABZzcQB+ABsAAABNAAAAAXEAfgAdc3EAfgAbAAAARgAAAAFzcQB+AHIAAAEAeHNyAEByZXBvcnQuY2FsbHJlc29sdXRpb24uQ2FsbFJlc29sdXRpb25UYWJsZVN1bW1hcnlJbmZvJERlZmF1bHRJbmZv3XK/8JXJObUCAAFMABFhcHBsaWNhdGlvblJlYXNvbnQAKExhbmFseXNpcy9pY2ZnL1N1bW1hcnlBcHBsaWNhdGlvblJlYXNvbjt4cgA0cmVwb3J0LmNhbGxyZXNvbHV0aW9uLkNhbGxSZXNvbHV0aW9uVGFibGVTdW1tYXJ5SW5mbxq20EbaZsyGAgABTAANaW5mbyRkZWxlZ2F0ZXEAfgA0eHBzcQB+ADZzcgAhZGF0YXN0cnVjdHVyZXMuTGlua2VkQXJyYXlIYXNoTWFwAAAAAAAAAAEDAAJGAApsb2FkRmFjdG9yTAAJaGFzaFRhYmxldAAuTGRhdGFzdHJ1Y3R1cmVzL2FycmF5aGFzaHRhYmxlL0FycmF5SGFzaFRhYmxlO3hwdwgAAAABQAAAAHQAGnN1bW1hcnkgYXBwbGljYXRpb24gcmVhc29udAA/ZGVjbGFyZWQgYXQgQmFzaWMuc3BlYzoyOjgzIHRvIGFwcGx5IHRvIGFsbCBjYWxscyB0byB0aGUgY2FsbGVleHNyAC9hbmFseXNpcy5pY2ZnLlN1bW1hcnlBcHBsaWNhdGlvblJlYXNvbiRTcGVjJEFsbIe5NEloSWp9AgACTAADbG9jcQB+AA1MAA9tZXRob2RTaWduYXR1cmVxAH4AGHhyACthbmFseXNpcy5pY2ZnLlN1bW1hcnlBcHBsaWNhdGlvblJlYXNvbiRTcGVj9gi37OrxUI4CAAB4cgAmYW5hbHlzaXMuaWNmZy5TdW1tYXJ5QXBwbGljYXRpb25SZWFzb25CnD+iq+g4mgIAAHhwcQB+ABp0ABVhZGQodWludDI1NiwgdWludDI1NilzcgATdmMuZGF0YS5UQUNNZXRhSW5mb0W7USKtClXbAgAGSQAFYmVnaW5JAANsZW5JAAZzb3VyY2VMAAdhZGRyZXNzdAAWTGphdmEvbWF0aC9CaWdJbnRlZ2VyO0wACGp1bXBUeXBldAATTGNvbXBpbGVyL0p1bXBUeXBlO0wADXNvdXJjZUNvbnRleHR0ABhMY29tcGlsZXIvU291cmNlQ29udGV4dDt4cAAAAEsAAAGpAAAAAHNyABRqYXZhLm1hdGguQmlnSW50ZWdlcoz8nx+pO/sdAwAGSQAIYml0Q291bnRJAAliaXRMZW5ndGhJABNmaXJzdE5vbnplcm9CeXRlTnVtSQAMbG93ZXN0U2V0Qml0SQAGc2lnbnVtWwAJbWFnbml0dWRldAACW0J4cQB+ADr///////////////7////+AAAAAXVyAAJbQqzzF/gGCFTgAgAAeHAAAAAQzkYEoAAAAAAAAAAAAAAAAXh+cgARY29tcGlsZXIuSnVtcFR5cGUAAAAAAAAAABIAAHhxAH4AVnQABUVOVEVSc3IAFmNvbXBpbGVyLlNvdXJjZUNvbnRleHSDeLXeEWLWywIAAkwAD2luZGV4VG9GaWxlUGF0aHQAD0xqYXZhL3V0aWwvTWFwO0wACXNvdXJjZURpcnEAfgAYeHBzcQB+APd3CAAAAAFAAAAAc3EAfgA5AAAAAHQAEFRlc3RDb250cmFjdC5zb2x4dAATLnBvc3RfYXV0b2ZpbmRlcnMuMHNxAH4A4XNxAH4AJgAAAAJ3BAAAAAJzcQB+AGtxAH4AK3EAfgArc3EAfgBidAAAc3EAfgByAAABAHNxAH4Aa3EAfgBacQB+AFpzcQB+AGJxAH4BGXNxAH4AcgAAAQB4c3EAfgDkc3EAfgDncQB+AOlxAH4A6nNxAH4AJgAAAAF3BAAAAAFzcQB+AOxzcQB+AGJxAH4BGXNxAH4AcgAAAQB4c3IAG2tvdGxpbi5jb2xsZWN0aW9ucy5FbXB0eVNldC9GsBV21+L0AgAAeHA="}
		AssignExpCmd calledContract!!42:10 R12:23
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.CVLFunctionStart","callIndex":4,"name":"cvl_add","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":1,"charByteOffset":82},"end":{"line":1,"charByteOffset":95}},"isNoRevert":true}}
		LabelCmd "9: Move primitive value for variable a542543:int..."
		LabelCmd "...done 9"
		AssignExpCmd CANON51:36 0x4(int)
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.CVLArg.PrimitiveArg","callIndex":4,"index":0,"sym":{"namePrefix":"CANON51","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":11,"charByteOffset":17},"end":{"line":11,"charByteOffset":26}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"a"}]},"param":{"Named_type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"id":"a","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":11,"charByteOffset":17},"end":{"line":11,"charByteOffset":26}}}}}
		LabelCmd "10: Move primitive value for variable b544545:int..."
		LabelCmd "...done 10"
		AssignExpCmd CANON52:37 0x5(int)
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.CVLArg.PrimitiveArg","callIndex":4,"index":1,"sym":{"namePrefix":"CANON52","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":11,"charByteOffset":28},"end":{"line":11,"charByteOffset":37}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"b"}]},"param":{"Named_type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"id":"b","range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":11,"charByteOffset":28},"end":{"line":11,"charByteOffset":37}}}}}
		AssignExpCmd:112 I43 0x4(int)
		AssignExpCmd:113 I44 0x5(int)
		AssignExpCmd:114 I45 0x9(int)
		AssignExpCmd:115 I46 0x9(int)
		AnnotationCmd:116 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Return","stmt":{"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":12,"charByteOffset":4},"end":{"line":12,"charByteOffset":34}},"exps":[{"#class":"spec.cvlast.CVLExp.CastExpr","toCastType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"arg":{"#class":"spec.cvlast.CVLExp.BinaryExp.AddExp","l":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"a","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":12,"charByteOffset":27},"end":{"line":12,"charByteOffset":28}}},"twoStateIndex":"NEITHER"},"r":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"b","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":12,"charByteOffset":31},"end":{"line":12,"charByteOffset":32}}},"twoStateIndex":"NEITHER"},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Mathint"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":12,"charByteOffset":27},"end":{"line":12,"charByteOffset":32}}}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":12,"charByteOffset":11},"end":{"line":12,"charByteOffset":32}}},"castType":"REQUIRE","inCVLBlockId":1}],"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.CVLRet.PrimitiveRet","callIndex":4,"index":0,"sym":{"namePrefix":"I46","tag":{"#class":"tac.Tag.Int"},"callIndex":0},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"label":{"stmt":{"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":12,"charByteOffset":4},"end":{"line":12,"charByteOffset":34}},"exps":[{"#class":"spec.cvlast.CVLExp.CastExpr","toCastType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"arg":{"#class":"spec.cvlast.CVLExp.BinaryExp.AddExp","l":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"a","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":12,"charByteOffset":27},"end":{"line":12,"charByteOffset":28}}},"twoStateIndex":"NEITHER"},"r":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"b","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":12,"charByteOffset":31},"end":{"line":12,"charByteOffset":32}}},"twoStateIndex":"NEITHER"},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Mathint"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":12,"charByteOffset":27},"end":{"line":12,"charByteOffset":32}}}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":12,"charByteOffset":11},"end":{"line":12,"charByteOffset":32}}},"castType":"REQUIRE","inCVLBlockId":1}],"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":27}
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.CVLFunctionEnd","callIndex":4,"name":"cvl_add"}}
		AnnotationCmd JSON{"key":{"name":"revert.confluence","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}
		LabelCmd "join point of revert handling"
		LabelCmd "8: Read primitive from tmp538539:int..."
		AssertCmd:117 true "sanity bounds check on cvl to vm encoding (unsigned int elements of a user array) of %1$s failed"
		AssignExpCmd R47:24 0x9
		LabelCmd "...done 8"
		AnnotationCmd JSON{"key":{"name":"call.trace.internal.summary.end","type":"analysis.icfg.SummaryStack$SummaryEnd$Internal","erasureStrategy":"Canonical"},"value":"rO0ABXNyAC5hbmFseXNpcy5pY2ZnLlN1bW1hcnlTdGFjayRTdW1tYXJ5RW5kJEludGVybmFs/bQ7d/THvhkCAANMAA9tZXRob2RTaWduYXR1cmV0ACZMc3BlYy9jdmxhc3QvUXVhbGlmaWVkTWV0aG9kU2lnbmF0dXJlO0wABHJldHN0ABBMamF2YS91dGlsL0xpc3Q7TAAHc3VwcG9ydHQAD0xqYXZhL3V0aWwvU2V0O3hyACVhbmFseXNpcy5pY2ZnLlN1bW1hcnlTdGFjayRTdW1tYXJ5RW5kFZQmA8fWa+kCAAB4cHNyADdzcGVjLmN2bGFzdC5RdWFsaWZpZWRNZXRob2RTaWduYXR1cmUkUXVhbGlmaWVkTWV0aG9kU2lnGH1MtG0dbPUCAANMAAZwYXJhbXNxAH4AAkwAE3F1YWxpZmllZE1ldGhvZE5hbWV0AChMc3BlYy9jdmxhc3QvQ29udHJhY3RGdW5jdGlvbklkZW50aWZpZXI7TAADcmVzcQB+AAJ4cHNyABNqYXZhLnV0aWwuQXJyYXlMaXN0eIHSHZnHYZ0DAAFJAARzaXpleHAAAAACdwQAAAACc3IAGXNwZWMuY3ZsYXN0LlZNUGFyYW0kTmFtZWT9C66+edYZbAIABEwABG5hbWV0ABJMamF2YS9sYW5nL1N0cmluZztMAAxvcmlnaW5hbE5hbWVxAH4ADEwABXJhbmdldAAWTHNwZWMvY3ZsYXN0L0NWTFJhbmdlO0wABnZtVHlwZXQALkxzcGVjL2N2bGFzdC90eXBlZGVzY3JpcHRvcnMvVk1UeXBlRGVzY3JpcHRvcjt4cgATc3BlYy5jdmxhc3QuVk1QYXJhbXyNTHZusLGIAgAAeHB0AAFhcQB+ABFzcgAac3BlYy5jdmxhc3QuQ1ZMUmFuZ2UkRW1wdHkKQULasOXTrwIAAUwAB2NvbW1lbnRxAH4ADHhyABRzcGVjLmN2bGFzdC5DVkxSYW5nZRrNE9gkPkLmAgAAeHB0AABzcgAzc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkVWTVR5cGVEZXNjcmlwdG9yJFVJbnRLqHosSzB6DiUCAAFJAAhiaXR3aWR0aHhyAERzcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRVZNVHlwZURlc2NyaXB0b3IkRVZNSXNvbW9ycGhpY1ZhbHVlVHlwZZbjlXdq3fF/AgAAeHIAOnNwZWMuY3ZsYXN0LnR5cGVkZXNjcmlwdG9ycy5FVk1UeXBlRGVzY3JpcHRvciRFVk1WYWx1ZVR5cGUQ5NL1qK834QIAAHhyAC1zcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRVZNVHlwZURlc2NyaXB0b3JeVh3cxo4+6AIAAHhwAAABAHNxAH4AC3QAAWJxAH4AHHNxAH4AEnEAfgAVc3EAfgAWAAABAHhzcgAdc3BlYy5jdmxhc3QuUXVhbGlmaWVkRnVuY3Rpb27lKUzy5DlRgwIAAkwABGhvc3R0AB5Mc3BlYy9jdmxhc3QvU29saWRpdHlDb250cmFjdDtMAAhtZXRob2RJZHEAfgAMeHBzcgAcc3BlYy5jdmxhc3QuU29saWRpdHlDb250cmFjdCNpfXcagT2iAgABTAAEbmFtZXEAfgAMeHB0AAxUZXN0Q29udHJhY3R0AANhZGRzcQB+AAkAAAABdwQAAAABc3IAG3NwZWMuY3ZsYXN0LlZNUGFyYW0kVW5uYW1lZAIPTbn85XVlAgACTAAFcmFuZ2VxAH4ADUwABnZtVHlwZXEAfgAOeHEAfgAPc3EAfgAScQB+ABVzcQB+ABYAAAEAeHNxAH4ACQAAAAF3BAAAAAFzcgAbYW5hbHlzaXMuaXAuSW50ZXJuYWxGdW5jUmV05InEVWrb2SYCAANJAAZvZmZzZXRMAAhsb2NhdGlvbnQAJ0xhbmFseXNpcy9pcC9JbnRlcm5hbEZ1bmNWYWx1ZUxvY2F0aW9uO0wAAXN0ABdMdmMvZGF0YS9UQUNTeW1ib2wkVmFyO3hwAAAAAHNyACxhbmFseXNpcy5pcC5JbnRlcm5hbEZ1bmNWYWx1ZUxvY2F0aW9uJFNjYWxhcurS/t67vyj1AgAAeHIAJWFuYWx5c2lzLmlwLkludGVybmFsRnVuY1ZhbHVlTG9jYXRpb25sjAqdSNnt+wIAAHhwc3IANXZjLmRhdGEuVEFDU3ltYm9sJFZhciRXaXRoRGVmYXVsdENhbGxJbmRleCRXaXRoQml0MjU2nq3gkxche2QCAAJMAARtZXRhdAAeTGNvbS9jZXJ0b3JhL2NvbGxlY3QvVHJlYXBNYXA7TAAKbmFtZVByZWZpeHEAfgAMeHIAFXZjLmRhdGEuVEFDU3ltYm9sJFZhcvxIa9S+MEYRAgAAeHIAEXZjLmRhdGEuVEFDU3ltYm9sE17/6RpKKNACAAB4cHNyACBjb20uY2VydG9yYS5jb2xsZWN0Lkhhc2hUcmVhcE1hcM4n+3qupXKcAgADTAADa2V5dAASTGphdmEvbGFuZy9PYmplY3Q7TAAEbmV4dHQAK0xjb20vY2VydG9yYS9jb2xsZWN0L0tleVZhbHVlUGFpckxpc3QkTW9yZTtMAAV2YWx1ZXEAfgA5eHIAJGNvbS5jZXJ0b3JhLmNvbGxlY3QuQWJzdHJhY3RUcmVhcE1hcC1u3UdoTQYZAgAAeHIAGWNvbS5jZXJ0b3JhLmNvbGxlY3QuVHJlYXD/3sPjttw/IwIAAkwABGxlZnR0ABtMY29tL2NlcnRvcmEvY29sbGVjdC9UcmVhcDtMAAVyaWdodHEAfgA9eHBzcQB+ADhwcHNyAAt0YWMuTWV0YUtleWr2F4pDsqLdAgADTAAPZXJhc3VyZVN0cmF0ZWd5dAAdTHRhYy9NZXRhS2V5JEVyYXN1cmVTdHJhdGVneTtMAARuYW1lcQB+AAxMAAN0eXB0ABFMamF2YS9sYW5nL0NsYXNzO3hwfnIAG3RhYy5NZXRhS2V5JEVyYXN1cmVTdHJhdGVneQAAAAAAAAAAEgAAeHIADmphdmEubGFuZy5FbnVtAAAAAAAAAAASAAB4cHQACUNhbm9uaWNhbHQAElRhYy5zeW1ib2wua2V5d29yZHZyACJ2Yy5kYXRhLlRBQ1N5bWJvbCRWYXIkS2V5d29yZEVudHJ5TuPA5DR23HYCAAB4cHBzcgAydmMuZGF0YS5UQUNTeW1ib2wkVmFyJEtleXdvcmRFbnRyeSRUQUNLZXl3b3JkRW50cnm4mRaPLAQsrQIAAkkAFm1heWJlVEFDS2V5d29yZE9yZGluYWxMAARuYW1lcQB+AAx4cQB+AEkAAAAtdAABTHBzcQB+AEBxAH4ARnQAEHRhYy5zdGFjay5oZWlnaHR2cgARamF2YS5sYW5nLkludGVnZXIS4qCk94GHOAIAAUkABXZhbHVleHIAEGphdmEubGFuZy5OdW1iZXKGrJUdC5TgiwIAAHhwcHNxAH4AUAAAA/90AANSNDd4c3IAImphdmEudXRpbC5Db2xsZWN0aW9ucyRTaW5nbGV0b25TZXQsUkGYKcCxvwIAAUwAB2VsZW1lbnRxAH4AOXhwcQB+ADc="}
		JumpCmd 5_0_0_2_0_0
	}
	Block 5_0_0_2_0_0 Succ [6_0_0_0_0_0] {
		AnnotationCmd:118 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":176,"bytecodeCount":8,"sources":[{"source":0,"begin":75,"end":500}]}}
		AnnotationCmd:111 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1180,"bytecodeCount":14,"sources":[{"source":1,"begin":957,"end":1179},{"source":1,"begin":1050,"end":1054},{"source":1,"begin":1088,"end":1090},{"source":1,"begin":1077,"end":1086},{"source":1,"begin":1073,"end":1091},{"source":1,"begin":1065,"end":1091},{"source":1,"begin":1101,"end":1172},{"source":1,"begin":1169,"end":1170},{"source":1,"begin":1158,"end":1167},{"source":1,"begin":1154,"end":1171},{"source":1,"begin":1145,"end":1151}]}}
		AnnotationCmd:111 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1165,"bytecodeCount":5,"sources":[{"source":1,"begin":833,"end":951},{"source":1,"begin":920,"end":944},{"source":1,"begin":938,"end":943}]}}
		AnnotationCmd:111 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1383,"bytecodeCount":9,"sources":[{"source":1,"begin":1850,"end":1927},{"source":1,"begin":1887,"end":1894},{"source":1,"begin":1916,"end":1921},{"source":1,"begin":1905,"end":1921},{"source":1,"begin":1895,"end":1927}]}}
		AnnotationCmd:111 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1174,"bytecodeCount":6,"sources":[{"source":1,"begin":920,"end":944},{"source":1,"begin":915,"end":918},{"source":1,"begin":908,"end":945},{"source":1,"begin":898,"end":951}]}}
		AnnotationCmd:93 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.EVMFunctionReturnWrite","returnbufOffset":"0","returnValueSym":{"#class":"vc.data.TACSymbol.Const","value":"9"},"callIndex":2}}
		AnnotationCmd:111 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1201,"bytecodeCount":6,"sources":[{"source":1,"begin":1101,"end":1172},{"source":1,"begin":1055,"end":1179}]}}
		AnnotationCmd:111 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":189,"bytecodeCount":8,"sources":[{"source":0,"begin":75,"end":500}]}}
		AssignExpCmd:93 lastHasThrown!!48:42 false
		AssignExpCmd:93 lastReverted!!49:6 false
		AnnotationCmd:119 JSON{"key":{"name":"tac.return.path","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}
		AnnotationCmd:93 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.HaltSnippet.Return","range":{"specFile":"TestContract.sol","start":{"line":5,"charByteOffset":4},"end":{"line":7,"charByteOffset":5}}}}
		LabelCmd:93 "End procedure TestContract-add(uint256,uint256)"
		LabelCmd:93 "0: Move primitive value for variable r2245:int..."
		AssignExpCmd:93 CANON26!!50:35 0x9
		LabelCmd:93 "...done 0"
		AnnotationCmd:93 JSON{"key":{"name":"call.trace.pop","type":"analysis.icfg.Inliner$CallStack$PopRecord","erasureStrategy":"Canonical"},"value":{"callee":{"contractId":"ce4604a0000000000000000000000001","sigHash":{"n":"771602f7"},"attr":{"#class":"scene.MethodAttribute.Common"}},"calleeId":2}}
	}
	Block 6_0_0_0_0_0 Succ [7_0_0_5_0_0] {
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageGlobalChangeSnippet.StorageTakeSnapshot","lhs":{"namePrefix":"lastStorage","tag":{"#class":"tac.Tag.BlockchainState"},"callIndex":0,"meta":[{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule"}},{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry","name":"lastStorage"}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.VMInternal.BlockchainState"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"lastStorage"}]}}}
		AnnotationCmd:93 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":26}
		AnnotationCmd:120 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Definition","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":37,"charByteOffset":4},"end":{"line":37,"charByteOffset":30}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"idL":[{"#class":"spec.cvlast.CVLLhs.Id","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":37,"charByteOffset":4},"end":{"line":37,"charByteOffset":14}},"id":"r3","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":37,"charByteOffset":4},"end":{"line":37,"charByteOffset":14}}}}],"exp":{"#class":"spec.cvlast.CVLExp.ApplyExp.ContractFunction.Concrete","methodIdWithCallContext":{"#class":"spec.cvlast.ConcreteMethod","signature":{"#class":"spec.cvlast.ExternalQualifiedMethodSignature.ExternalQualifiedMethodSig","wrapped":{"#class":"spec.cvlast.QualifiedMethodSignature.QualifiedMethodSig","qualifiedMethodName":{"#class":"spec.cvlast.QualifiedFunction","host":{"name":"TestContract"},"methodId":"double"},"params":[{"#class":"spec.cvlast.VMParam.Named","name":"d","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}}],"res":[{"#class":"spec.cvlast.VMParam.Unnamed","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}}]},"sighashInt":{"n":"eee97206"}}},"args":[{"#class":"spec.cvlast.CVLExp.VariableExp","id":"e","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":37,"charByteOffset":24},"end":{"line":37,"charByteOffset":25}}},"twoStateIndex":"NEITHER"},{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"7","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"7"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":37,"charByteOffset":27},"end":{"line":37,"charByteOffset":28}}}}],"noRevert":true,"storage":{"id":"lastStorage","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.VMInternal.BlockchainState"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Empty","comment":"empty storage type"}},"twoStateIndex":"NEITHER"},"isWhole":false,"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.ReturnValue"}},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":37,"charByteOffset":17},"end":{"line":37,"charByteOffset":29}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.CallResolution$DirectPassing","target":{"methodSignature":{"#class":"spec.cvlast.ExternalQualifiedMethodSignature.ExternalQualifiedMethodSig","wrapped":{"#class":"spec.cvlast.QualifiedMethodSignature.QualifiedMethodSig","qualifiedMethodName":{"#class":"spec.cvlast.QualifiedFunction","host":{"name":"TestContract"},"methodId":"double"},"params":[{"#class":"spec.cvlast.VMParam.Named","name":"d","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}}],"res":[{"#class":"spec.cvlast.VMParam.Unnamed","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}}]},"sighashInt":{"n":"eee97206"}},"definitelyNonPayable":true,"annotation":{"visibility":"EXTERNAL","envFree":false,"library":false,"virtual":false},"stateMutability":"nonpayable","evmExternalMethodInfo":{"sigHash":"eee97206","name":"double","argTypes":[{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}],"resultTypes":[{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}],"stateMutability":"nonpayable","isConstant":false,"paramNames":["d"],"isLibrary":false,"contractName":"TestContract","contractInstanceId":"ce4604a0000000000000000000000001","sourceSegment":{"range":{"specFile":"TestContract.sol","start":{"line":9,"charByteOffset":4},"end":{"line":11,"charByteOffset":5}},"content":"function double(uint256 d) public returns (uint256) {\n        return 2 * d;\n    }"}}},"hasEnv":true}}},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AnnotationCmd JSON{"key":{"name":"cvl.trace.data.movement","type":"spec.CVLCompiler$Companion$TraceMeta$CVLMovement","erasureStrategy":"Erased"},"value":{"dst":{"id":"certoraArg362363"},"src":{"id":"e230"}}}
		AssignExpCmd:121 I52 0x7
	}
	Block 7_0_0_5_0_0 Succ [8_0_0_6_0_0] {
		AssignHavocCmd:122 CANON59!!53:17
		AnnotationCmd:122 JSON{"key":{"name":"call.trace.push","type":"analysis.icfg.Inliner$CallStack$PushRecord","erasureStrategy":"Canonical"},"value":{"callee":{"contractId":"ce4604a0000000000000000000000001","sigHash":{"n":"eee97206"},"attr":{"#class":"scene.MethodAttribute.Common"}},"summary":null,"convention":{"#class":"analysis.icfg.Inliner.CallConventionType.FromCVL"},"calleeId":5}}
		AssignHavocCmd:122 tacCalldatasize!!54:9
		AssumeExpCmd Eq(tacCalldatasize!!54:9 0x24 )
		AssignExpCmd:122 tacCalldatabuf@5:15 MapDefinition(CANON60:bv256 -> Ite(Lt(CANON60 tacCalldatasize!!54:9 ) Select(Select(Select(CANON28!7:25 CANON60 ) tacCalldatasize!!54:9 ) 0xeee97206 ) 0x0 ) bytemap)
		AssignExpCmd:122 R55:20 Select(Select(Select(CANON28!7:25 0x0 ) 0x24 ) 0xeee97206 )
		AssumeExpCmd LAnd(Ge(R55:20 0xeee9720600000000000000000000000000000000000000000000000000000000 ) Le(R55:20 0xeee97206ffffffffffffffffffffffffffffffffffffffffffffffffffffffff ) )
		AnnotationCmd:122 JSON{"key":{"name":"cvl.arg-serialization.start","type":"spec.CVLInvocationCompiler$StartSerializationMarker","erasureStrategy":"Canonical"},"value":{"id":1,"callId":5}}
		LabelCmd:122 "4: Read primitive from certoraArg364365:int..."
		AssertCmd:123 true "sanity bounds check on cvl to vm encoding (unsigned int elements of a user array) of %1$s failed"
		AssertCmd:123 true "sanity bounds check on cvl to vm encoding (unsigned int elements of a user array) of %1$s failed"
		AssignExpCmd:122 tacCalldatabufCANON0@5:2 0x7
		LabelCmd:122 "...done 4"
		AnnotationCmd JSON{"key":{"name":"cvl.trace.external","type":"spec.CVLCompiler$Companion$TraceMeta$ExternalArg","erasureStrategy":"Erased"},"value":{"s":{"#class":"spec.CVLCompiler.Companion.TraceMeta.ValueIdentity.TACVar","t":{"namePrefix":"I52","tag":{"#class":"tac.Tag.Int"},"callIndex":0}},"rootOffset":"0","callId":5,"targetType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"sourceType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"7"},"fields":null}}
		AnnotationCmd:122 JSON{"key":{"name":"cvl.arg-serialization.end","type":"spec.CVLInvocationCompiler$EndSerializationMarker","erasureStrategy":"Canonical"},"value":{"id":1,"callId":5}}
		AssignExpCmd:122 lastHasThrown!!56:42 false
		AssertCmd:124 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:125 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:126 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:127 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:128 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:129 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:130 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:131 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:132 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:133 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:134 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssertCmd:135 true "sanity bounds check on cvl to vm encoding (unsigned int) of %1$s failed"
		AssignExpCmd:122 R58:20 Apply(safe_math_narrow_bv256:bif CANON4:43)
		AssignExpCmd:122 R60:20 Select(tacBalance!!40:13 Apply(to_skey:bif R58:20) )
		AssignExpCmd:136 tacBalance!!62:13 Store(tacBalance!!40:13 Apply(to_skey:bif R58:20) R60:20 )
		AssignExpCmd:122 R63:20 Select(tacBalance!!62:13 Apply(to_skey:bif R12:23) )
		AssignExpCmd:136 R65:20 Apply(safe_math_narrow_bv256:bif R63:20)
		AnnotationCmd:122 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.TransferSnippet","srcAccountInfo":{"old":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R60","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"new":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R60","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"addr":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R58","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]}},"trgAccountInfo":{"old":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R63","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"new":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R65","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"addr":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R12","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry","name":"tacContractAt"}},{"key":{"name":"tac.contract.sym.addr.name","type":"java.lang.String","erasureStrategy":"Erased"},"value":"TestContract"},{"key":{"name":"tac.contract.sym.addr","type":"java.math.BigInteger","erasureStrategy":"Erased"},"value":"ce4604a0000000000000000000000001"}]}},"transferredAmount":{"#class":"vc.data.TACSymbol.Const","value":"0"}}}
		LabelCmd:122 "Start procedure TestContract-double(uint256)"
		AnnotationCmd:122 JSON{"key":{"name":"fps.free-pointer-is-scalarized","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true}
		AssignExpCmd:122 R66:20 Select(tacExtcodesize!!4:7 Apply(to_skey:bif R12:109) )
		AssumeExpCmd Ge(R66:20 0x1 )
		AnnotationCmd:122 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.RawStorageAccess.WithLocSym","isLoad":true,"loc":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R12","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"tacAddress","maybeTACKeywordOrdinal":22}},{"key":{"name":"tac.env.known-bit-width","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":160},{"key":{"name":"tac.contract.sym.addr.name","type":"java.lang.String","erasureStrategy":"Erased"},"value":"TestContract"},{"key":{"name":"tac.contract.sym.addr","type":"java.math.BigInteger","erasureStrategy":"Erased"},"value":"ce4604a0000000000000000000000001"}]},"contractInstance":"ce4604a0000000000000000000000001","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R66","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"storageType":null,"range":null}}
		AnnotationCmd:122 JSON{"key":{"name":"internal.func.finder.info","type":"analysis.ip.InternalFunctionFinderReport","erasureStrategy":"Erased"},"value":{"unresolvedFunctions":[]}}
		AnnotationCmd:122 JSON{"key":{"name":"fps.free-pointer-is-scalarized","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true}
		AnnotationCmd:122 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":0,"bytecodeCount":8,"sources":[{"source":0,"begin":25,"end":2021}]}}
		LabelCmd "→ Assuming FP is strictly monotonic increasing"
		LabelCmd "←"
		AnnotationCmd:122 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.StartBranchSnippet","branchIndex":2,"branchSource":{"range":{"specFile":"TestContract.sol","start":{"line":2,"charByteOffset":0},"end":{"line":24,"charByteOffset":1}},"content":"contract TestContract {...}"}}}
		AnnotationCmd:122 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.EndBranchSnippet","branchIndex":2}}
		AnnotationCmd:137 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":16,"bytecodeCount":7,"sources":[{"source":0,"begin":25,"end":2021}]}}
		AnnotationCmd:137 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":26,"bytecodeCount":9,"sources":[{"source":0,"begin":25,"end":2021}]}}
		AnnotationCmd:137 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":43,"bytecodeCount":5,"sources":[{"source":0,"begin":25,"end":2021}]}}
		AnnotationCmd:137 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":54,"bytecodeCount":5,"sources":[{"source":0,"begin":25,"end":2021}]}}
		AnnotationCmd:137 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":65,"bytecodeCount":5,"sources":[{"source":0,"begin":25,"end":2021}]}}
		AnnotationCmd:137 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":76,"bytecodeCount":5,"sources":[{"source":0,"begin":25,"end":2021}]}}
		AnnotationCmd:137 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":208,"bytecodeCount":14,"sources":[{"source":0,"begin":506,"end":923}]}}
		AnnotationCmd:138 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1064,"bytecodeCount":10,"sources":[{"source":1,"begin":152,"end":414},{"source":1,"begin":211,"end":217},{"source":1,"begin":260,"end":262},{"source":1,"begin":248,"end":257},{"source":1,"begin":239,"end":246},{"source":1,"begin":235,"end":258},{"source":1,"begin":231,"end":263},{"source":1,"begin":228,"end":230}]}}
		AnnotationCmd:122 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.StartBranchSnippet","branchIndex":3,"branchSource":{"range":{"specFile":"TestContract.sol","start":{"line":9,"charByteOffset":4},"end":{"line":11,"charByteOffset":5}},"content":"compiler-generate condition in function double(uint256 d) public returns (uint256) "}}}
		AnnotationCmd:122 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.EndBranchSnippet","branchIndex":3}}
		AnnotationCmd:122 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1082,"bytecodeCount":9,"sources":[{"source":1,"begin":228,"end":230},{"source":1,"begin":319,"end":320},{"source":1,"begin":344,"end":397},{"source":1,"begin":389,"end":396},{"source":1,"begin":380,"end":386},{"source":1,"begin":369,"end":378},{"source":1,"begin":365,"end":387}]}}
		AnnotationCmd:122 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1043,"bytecodeCount":10,"sources":[{"source":1,"begin":7,"end":146},{"source":1,"begin":53,"end":58},{"source":1,"begin":91,"end":97},{"source":1,"begin":78,"end":98},{"source":1,"begin":69,"end":98},{"source":1,"begin":107,"end":140},{"source":1,"begin":134,"end":139}]}}
		AnnotationCmd:122 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1440,"bytecodeCount":5,"sources":[{"source":1,"begin":2119,"end":2241},{"source":1,"begin":2192,"end":2216},{"source":1,"begin":2210,"end":2215}]}}
		AnnotationCmd:122 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1383,"bytecodeCount":9,"sources":[{"source":1,"begin":1850,"end":1927},{"source":1,"begin":1887,"end":1894},{"source":1,"begin":1916,"end":1921},{"source":1,"begin":1905,"end":1921},{"source":1,"begin":1895,"end":1927}]}}
		AnnotationCmd:122 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1449,"bytecodeCount":5,"sources":[{"source":1,"begin":2192,"end":2216},{"source":1,"begin":2185,"end":2190},{"source":1,"begin":2182,"end":2217},{"source":1,"begin":2172,"end":2174}]}}
		AnnotationCmd:122 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1460,"bytecodeCount":3,"sources":[{"source":1,"begin":2172,"end":2174},{"source":1,"begin":2162,"end":2241}]}}
		AnnotationCmd:122 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1058,"bytecodeCount":6,"sources":[{"source":1,"begin":107,"end":140},{"source":1,"begin":59,"end":146}]}}
		AnnotationCmd:122 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1096,"bytecodeCount":9,"sources":[{"source":1,"begin":344,"end":397},{"source":1,"begin":334,"end":397},{"source":1,"begin":290,"end":407},{"source":1,"begin":218,"end":414}]}}
		AnnotationCmd:122 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":229,"bytecodeCount":3,"sources":[{"source":0,"begin":506,"end":923}]}}
		JumpCmd 8_0_0_6_0_0
	}
	Block 8_0_0_6_0_0 Succ [9_0_0_5_0_0] {
		AnnotationCmd JSON{"key":{"name":"call.trace.internal.summary.start","type":"analysis.icfg.SummaryStack$SummaryStart$Internal","erasureStrategy":"CallTrace"},"value":"rO0ABXNyADBhbmFseXNpcy5pY2ZnLlN1bW1hcnlTdGFjayRTdW1tYXJ5U3RhcnQkSW50ZXJuYWze2wAmittJZwIABUwADmFwcGxpZWRTdW1tYXJ5dAAsTGFuYWx5c2lzL2ljZmcvU3VtbWFyaXphdGlvbiRBcHBsaWVkU3VtbWFyeTtMABdjYWxsUmVzb2x1dGlvblRhYmxlSW5mb3QANkxyZXBvcnQvY2FsbHJlc29sdXRpb24vQ2FsbFJlc29sdXRpb25UYWJsZVN1bW1hcnlJbmZvO0wAC2NhbGxTaXRlU3JjdAAVTHZjL2RhdGEvVEFDTWV0YUluZm87TAAPbWV0aG9kU2lnbmF0dXJldAAmTHNwZWMvY3ZsYXN0L1F1YWxpZmllZE1ldGhvZFNpZ25hdHVyZTtMAAdzdXBwb3J0dAAPTGphdmEvdXRpbC9TZXQ7eHIAJ2FuYWx5c2lzLmljZmcuU3VtbWFyeVN0YWNrJFN1bW1hcnlTdGFydM6P29O9R0c9AgAAeHBzcgA3YW5hbHlzaXMuaWNmZy5TdW1tYXJpemF0aW9uJEFwcGxpZWRTdW1tYXJ5JE1ldGhvZHNCbG9ja8QZaUG9nkK8AgACTAAMc3BlY0NhbGxTdW1tdAAuTHNwZWMvY3ZsYXN0L1NwZWNDYWxsU3VtbWFyeSRFeHByZXNzaWJsZUluQ1ZMO0wAEHN1bW1hcml6ZWRNZXRob2R0ABtMc3BlYy9DVkwkU3VtbWFyeVNpZ25hdHVyZTt4cHNyAB9zcGVjLmN2bGFzdC5TcGVjQ2FsbFN1bW1hcnkkRXhwBa/ML1lm2f4CAAdMAAhjdmxSYW5nZXQAFkxzcGVjL2N2bGFzdC9DVkxSYW5nZTtMAANleHB0ABRMc3BlYy9jdmxhc3QvQ1ZMRXhwO0wADGV4cGVjdGVkVHlwZXQAEExqYXZhL3V0aWwvTGlzdDtMAAlmdW5QYXJhbXNxAH4AD0wABXNjb3BldAAWTHNwZWMvY3ZsYXN0L0NWTFNjb3BlO0wAEXN1bW1hcml6YXRpb25Nb2RldAAvTHNwZWMvY3ZsYXN0L1NwZWNDYWxsU3VtbWFyeSRTdW1tYXJpemF0aW9uTW9kZTtMAAp3aXRoQ2xhdXNldAAsTHNwZWMvY3ZsYXN0L1NwZWNDYWxsU3VtbWFyeSRFeHAkV2l0aENsYXVzZTt4cgAsc3BlYy5jdmxhc3QuU3BlY0NhbGxTdW1tYXJ5JEV4cHJlc3NpYmxlSW5DVkwEHG3pUuDAOwIAAHhyABtzcGVjLmN2bGFzdC5TcGVjQ2FsbFN1bW1hcnmf4QieXcWlAQIAAHhwc3IAGnNwZWMuY3ZsYXN0LkNWTFJhbmdlJFJhbmdlpjwN4KUDjBsCAANMAANlbmR0ABZMdXRpbHMvU291cmNlUG9zaXRpb247TAAIc3BlY0ZpbGV0ABJMamF2YS9sYW5nL1N0cmluZztMAAVzdGFydHEAfgAXeHIAFHNwZWMuY3ZsYXN0LkNWTFJhbmdlGs0T2CQ+QuYCAAB4cHNyABR1dGlscy5Tb3VyY2VQb3NpdGlvbpX059TqmcSNAgACSQAOY2hhckJ5dGVPZmZzZXRJAARsaW5leHAAAABZAAAAAnQACkJhc2ljLnNwZWNzcQB+ABsAAABKAAAAAnNyACBzcGVjLmN2bGFzdC5DVkxFeHAkQXJyYXlEZXJlZkV4cOQk2+BsCGAGAgADTAAFYXJyYXlxAH4ADkwABWluZGV4cQB+AA5MAAN0YWd0ABdMc3BlYy9jdmxhc3QvQ1ZMRXhwVGFnO3hyABJzcGVjLmN2bGFzdC5DVkxFeHCM/spMMCiwgAIAAHhwc3IAHnNwZWMuY3ZsYXN0LkNWTEV4cCRWYXJpYWJsZUV4cJ0ULkp52IKNAgAETAACaWRxAH4AGEwADG9yaWdpbmFsTmFtZXEAfgAYTAADdGFncQB+ACBMAA10d29TdGF0ZUluZGV4dAAbTHNwZWMvY3ZsYXN0L1R3b1N0YXRlSW5kZXg7eHEAfgAhdAAMZ2hvc3RfZG91YmxlcQB+ACZzcgAVc3BlYy5jdmxhc3QuQ1ZMRXhwVGFnDcAz2goEJwACAAVaAAloYXNQYXJlbnNMAAphbm5vdGF0aW9udAAiTHNwZWMvY3ZsYXN0L0V4cHJlc3Npb25Bbm5vdGF0aW9uO0wACGN2bFJhbmdlcQB+AA1MAAVzY29wZXEAfgAQTAAEdHlwZXQAFUxzcGVjL2N2bGFzdC9DVkxUeXBlO3hwAHBzcQB+ABZzcQB+ABsAAABWAAAAAnEAfgAdc3EAfgAbAAAASgAAAAJzcgAUc3BlYy5jdmxhc3QuQ1ZMU2NvcGUiyWBY1B1dVAIAA0wAFmhhc2hDb2RlQ2FjaGUkZGVsZWdhdGV0AA1Ma290bGluL0xhenk7TAAKaW5uZXJTY29wZXEAfgAQTAAKc2NvcGVTdGFja3EAfgAPeHBzcgAaa290bGluLkluaXRpYWxpemVkTGF6eUltcGx7x3/xICqBjQIAAUwABXZhbHVldAASTGphdmEvbGFuZy9PYmplY3Q7eHBzcgARamF2YS5sYW5nLkludGVnZXIS4qCk94GHOAIAAUkABXZhbHVleHIAEGphdmEubGFuZy5OdW1iZXKGrJUdC5TgiwIAAHhwzPGofnNxAH4ALnNxAH4AMXNxAH4ANE5njWFzcQB+AC5zcQB+ADFzcQB+ADQAAAAfcHNyABxrb3RsaW4uY29sbGVjdGlvbnMuRW1wdHlMaXN0mW/H0KfgYDICAAB4cHNyACNqYXZhLnV0aWwuQ29sbGVjdGlvbnMkU2luZ2xldG9uTGlzdCrvKRA8p5uXAgABTAAHZWxlbWVudHEAfgAyeHBzcgAmc3BlYy5jdmxhc3QuQ1ZMU2NvcGUkSXRlbSRBc3RTY29wZUl0ZW2Hm6f3BtWhkwIAAHhyABlzcGVjLmN2bGFzdC5DVkxTY29wZSRJdGVtLwOv/543VkUCAAB4cHNyABNqYXZhLnV0aWwuQXJyYXlMaXN0eIHSHZnHYZ0DAAFJAARzaXpleHAAAAACdwQAAAACcQB+AENzcgArc3BlYy5jdmxhc3QuQ1ZMU2NvcGUkSXRlbSRFeHByZXNzaW9uU3VtbWFyeQ8zGp1aX6loAgABSQAHc2NvcGVJZHhyAClzcGVjLmN2bGFzdC5DVkxTY29wZSRJdGVtJEFTVEVsZW1lbnRTY29wZVKrjxFR5CKWAgABTAAHZWxlbWVudHQAGkxzcGVjL2N2bGFzdC9DcmVhdGVzU2NvcGU7eHEAfgBCc3EAfgAMcQB+ABpzcQB+AB9zcQB+ACNxAH4AJnEAfgAmc3EAfgAnAHBxAH4AK3EAfgAwcH5yABlzcGVjLmN2bGFzdC5Ud29TdGF0ZUluZGV4AAAAAAAAAAASAAB4cgAOamF2YS5sYW5nLkVudW0AAAAAAAAAABIAAHhwdAAHTkVJVEhFUnNxAH4AI3QAAWRxAH4AU3NxAH4AJwBwc3EAfgAWc3EAfgAbAAAAWAAAAAJxAH4AHXNxAH4AGwAAAFcAAAACcQB+ADBwcQB+AFBzcQB+ACcAcHNxAH4AFnNxAH4AGwAAAFkAAAACcQB+AB1zcQB+ABsAAABKAAAAAnEAfgAwcHBzcQB+AEQAAAABdwQAAAABc3IAGXNwZWMuY3ZsYXN0LlZNUGFyYW0kTmFtZWT9C66+edYZbAIABEwABG5hbWVxAH4AGEwADG9yaWdpbmFsTmFtZXEAfgAYTAAFcmFuZ2VxAH4ADUwABnZtVHlwZXQALkxzcGVjL2N2bGFzdC90eXBlZGVzY3JpcHRvcnMvVk1UeXBlRGVzY3JpcHRvcjt4cgATc3BlYy5jdmxhc3QuVk1QYXJhbXyNTHZusLGIAgAAeHBxAH4AU3EAfgBTc3EAfgAWc3EAfgAbAAAAKgAAAAJxAH4AHXNxAH4AGwAAACEAAAACc3IAM3NwZWMuY3ZsYXN0LnR5cGVkZXNjcmlwdG9ycy5FVk1UeXBlRGVzY3JpcHRvciRVSW50S6h6LEsweg4lAgABSQAIYml0d2lkdGh4cgBEc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkVWTVR5cGVEZXNjcmlwdG9yJEVWTUlzb21vcnBoaWNWYWx1ZVR5cGWW45V3at3xfwIAAHhyADpzcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRVZNVHlwZURlc2NyaXB0b3IkRVZNVmFsdWVUeXBlEOTS9aivN+ECAAB4cgAtc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkVWTVR5cGVEZXNjcmlwdG9yXlYd3MaOPugCAAB4cAAAAQB4cQB+ADB+cgAtc3BlYy5jdmxhc3QuU3BlY0NhbGxTdW1tYXJ5JFN1bW1hcml6YXRpb25Nb2RlAAAAAAAAAAASAAB4cQB+AE90AANBTExwAAAAAXhzcgAtc3BlYy5jdmxhc3QuQ1ZMVHlwZSRQdXJlQ1ZMVHlwZSRHaG9zdCRNYXBwaW5nC/AH6dx8OD0CAAJMAANrZXl0ACFMc3BlYy9jdmxhc3QvQ1ZMVHlwZSRQdXJlQ1ZMVHlwZTtMAAV2YWx1ZXEAfgBteHIAJXNwZWMuY3ZsYXN0LkNWTFR5cGUkUHVyZUNWTFR5cGUkR2hvc3Sz1/KRRxkpuAIAAHhyAB9zcGVjLmN2bGFzdC5DVkxUeXBlJFB1cmVDVkxUeXBl/Qa0FlO2KLECAAB4cgATc3BlYy5jdmxhc3QuQ1ZMVHlwZXQxE5W3wWVQAgAAeHBzcgAvc3BlYy5jdmxhc3QuQ1ZMVHlwZSRQdXJlQ1ZMVHlwZSRQcmltaXRpdmUkVUludEu5C5qOKRJGKQIAAkkACGJpdFdpZHRoSQABa3hyAClzcGVjLmN2bGFzdC5DVkxUeXBlJFB1cmVDVkxUeXBlJFByaW1pdGl2ZQqb2/80fsI7AgAAeHEAfgBvAAABAAAAAQBzcQB+AHIAAAEAAAABAHEAfgBQc3EAfgAjcQB+AFNxAH4AU3NxAH4AJwBwcQB+AFVxAH4AMHNyABZzcGVjLmN2bGFzdC5DVkxUeXBlJFZNo6s7LR18330CAAJMAAdjb250ZXh0dAArTHNwZWMvY3ZsYXN0L3R5cGVkZXNjcmlwdG9ycy9Gcm9tVk1Db250ZXh0O0wACmRlc2NyaXB0b3JxAH4AXnhxAH4AcHNyAENzcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRnJvbVZNQ29udGV4dCRJbnRlcm5hbFN1bW1hcnlBcmdCaW5kaW5nnsXkzwE/iScCAAB4cgApc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkZyb21WTUNvbnRleHTF2vGG93fwZQIAAHhwcQB+AGhxAH4AUHNxAH4AJwBwcQB+AFlxAH4AMHEAfgB1cHNxAH4ARAAAAAF3BAAAAAFxAH4AYHhxAH4AMHEAfgBqcHNyABZzcGVjLkNWTCRJbnRlcm5hbEV4YWN0hfxIIfCO7GACAAFMAAlzaWduYXR1cmV0AC9Mc3BlYy9jdmxhc3QvUXVhbGlmaWVkTWV0aG9kUGFyYW1ldGVyU2lnbmF0dXJlO3hwc3IAN3NwZWMuY3ZsYXN0LlF1YWxpZmllZE1ldGhvZFNpZ25hdHVyZSRRdWFsaWZpZWRNZXRob2RTaWcYfUy0bR1s9QIAA0wABnBhcmFtc3EAfgAPTAATcXVhbGlmaWVkTWV0aG9kTmFtZXQAKExzcGVjL2N2bGFzdC9Db250cmFjdEZ1bmN0aW9uSWRlbnRpZmllcjtMAANyZXNxAH4AD3hwcQB+AFxzcgAdc3BlYy5jdmxhc3QuUXVhbGlmaWVkRnVuY3Rpb27lKUzy5DlRgwIAAkwABGhvc3R0AB5Mc3BlYy9jdmxhc3QvU29saWRpdHlDb250cmFjdDtMAAhtZXRob2RJZHEAfgAYeHBzcgAcc3BlYy5jdmxhc3QuU29saWRpdHlDb250cmFjdCNpfXcagT2iAgABTAAEbmFtZXEAfgAYeHB0AAxUZXN0Q29udHJhY3R0AAZkb3VibGVzcQB+AEQAAAABdwQAAAABc3IAG3NwZWMuY3ZsYXN0LlZNUGFyYW0kVW5uYW1lZAIPTbn85XVlAgACTAAFcmFuZ2VxAH4ADUwABnZtVHlwZXEAfgBeeHEAfgBfc3EAfgAWc3EAfgAbAAAARQAAAAJxAH4AHXNxAH4AGwAAAD4AAAACc3EAfgBkAAABAHhzcgBAcmVwb3J0LmNhbGxyZXNvbHV0aW9uLkNhbGxSZXNvbHV0aW9uVGFibGVTdW1tYXJ5SW5mbyREZWZhdWx0SW5mb91yv/CVyTm1AgABTAARYXBwbGljYXRpb25SZWFzb250AChMYW5hbHlzaXMvaWNmZy9TdW1tYXJ5QXBwbGljYXRpb25SZWFzb247eHIANHJlcG9ydC5jYWxscmVzb2x1dGlvbi5DYWxsUmVzb2x1dGlvblRhYmxlU3VtbWFyeUluZm8attBG2mbMhgIAAUwADWluZm8kZGVsZWdhdGVxAH4AL3hwc3EAfgAxc3IAIWRhdGFzdHJ1Y3R1cmVzLkxpbmtlZEFycmF5SGFzaE1hcAAAAAAAAAABAwACRgAKbG9hZEZhY3RvckwACWhhc2hUYWJsZXQALkxkYXRhc3RydWN0dXJlcy9hcnJheWhhc2h0YWJsZS9BcnJheUhhc2hUYWJsZTt4cHcIAAAAAUAAAAB0ABpzdW1tYXJ5IGFwcGxpY2F0aW9uIHJlYXNvbnQAP2RlY2xhcmVkIGF0IEJhc2ljLnNwZWM6Mzo3NSB0byBhcHBseSB0byBhbGwgY2FsbHMgdG8gdGhlIGNhbGxlZXhzcgAvYW5hbHlzaXMuaWNmZy5TdW1tYXJ5QXBwbGljYXRpb25SZWFzb24kU3BlYyRBbGyHuTRJaElqfQIAAkwAA2xvY3EAfgANTAAPbWV0aG9kU2lnbmF0dXJlcQB+ABh4cgArYW5hbHlzaXMuaWNmZy5TdW1tYXJ5QXBwbGljYXRpb25SZWFzb24kU3BlY/YIt+zq8VCOAgAAeHIAJmFuYWx5c2lzLmljZmcuU3VtbWFyeUFwcGxpY2F0aW9uUmVhc29uQpw/oqvoOJoCAAB4cHEAfgAadAAPZG91YmxlKHVpbnQyNTYpc3IAE3ZjLmRhdGEuVEFDTWV0YUluZm9Fu1EirQpV2wIABkkABWJlZ2luSQADbGVuSQAGc291cmNlTAAHYWRkcmVzc3QAFkxqYXZhL21hdGgvQmlnSW50ZWdlcjtMAAhqdW1wVHlwZXQAE0xjb21waWxlci9KdW1wVHlwZTtMAA1zb3VyY2VDb250ZXh0dAAYTGNvbXBpbGVyL1NvdXJjZUNvbnRleHQ7eHAAAAH6AAABoQAAAABzcgAUamF2YS5tYXRoLkJpZ0ludGVnZXKM/J8fqTv7HQMABkkACGJpdENvdW50SQAJYml0TGVuZ3RoSQATZmlyc3ROb256ZXJvQnl0ZU51bUkADGxvd2VzdFNldEJpdEkABnNpZ251bVsACW1hZ25pdHVkZXQAAltCeHEAfgA1///////////////+/////gAAAAF1cgACW0Ks8xf4BghU4AIAAHhwAAAAEM5GBKAAAAAAAAAAAAAAAAF4fnIAEWNvbXBpbGVyLkp1bXBUeXBlAAAAAAAAAAASAAB4cQB+AE90AAVFTlRFUnNyABZjb21waWxlci5Tb3VyY2VDb250ZXh0g3i13hFi1ssCAAJMAA9pbmRleFRvRmlsZVBhdGh0AA9MamF2YS91dGlsL01hcDtMAAlzb3VyY2VEaXJxAH4AGHhwc3EAfgCZdwgAAAABQAAAAHNxAH4ANAAAAAB0ABBUZXN0Q29udHJhY3Quc29seHQAEy5wb3N0X2F1dG9maW5kZXJzLjBzcQB+AINzcQB+AEQAAAABdwQAAAABc3EAfgBdcQB+AFNxAH4AU3NyABpzcGVjLmN2bGFzdC5DVkxSYW5nZSRFbXB0eQpBQtqw5dOvAgABTAAHY29tbWVudHEAfgAYeHEAfgAZdAAAc3EAfgBkAAABAHhzcQB+AIZzcQB+AIlxAH4Ai3EAfgCMc3EAfgBEAAAAAXcEAAAAAXNxAH4AjnNxAH4AunEAfgC8c3EAfgBkAAABAHhzcgAba290bGluLmNvbGxlY3Rpb25zLkVtcHR5U2V0L0awFXbX4vQCAAB4cA=="}
		AssignExpCmd calledContract!!67:10 R12:23
		LabelCmd "7: Move primitive value for variable tmp534535:int..."
		AssignExpCmd I68 0x7
		LabelCmd "...done 7"
		AssignExpCmd CANON83:39 Select(CANON84:40 0x7(int) )
		AssumeExpCmd LAnd(Ge(CANON83:39 0x0(int) ) Le(CANON83:39 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.GhostRead","readValue":{"namePrefix":"CANON83","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.ghost","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true}]},"indices":[{"namePrefix":"I68","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}],"name":"ghost_double","sort":{"#class":"spec.cvlast.GhostSort.Mapping"},"persistent":false,"range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":2,"charByteOffset":74},"end":{"line":2,"charByteOffset":89}},"readExpr":"ghost_double[d]"}}
		LabelCmd "6: Read primitive from tmp532533:int..."
		AssertCmd:139 true "sanity bounds check on cvl to vm encoding (unsigned int elements of a user array) of %1$s failed"
		AssignExpCmd R69:24 Apply(safe_math_narrow_bv256:bif CANON83)
		LabelCmd "...done 6"
		AnnotationCmd JSON{"key":{"name":"call.trace.internal.summary.end","type":"analysis.icfg.SummaryStack$SummaryEnd$Internal","erasureStrategy":"Canonical"},"value":"rO0ABXNyAC5hbmFseXNpcy5pY2ZnLlN1bW1hcnlTdGFjayRTdW1tYXJ5RW5kJEludGVybmFs/bQ7d/THvhkCAANMAA9tZXRob2RTaWduYXR1cmV0ACZMc3BlYy9jdmxhc3QvUXVhbGlmaWVkTWV0aG9kU2lnbmF0dXJlO0wABHJldHN0ABBMamF2YS91dGlsL0xpc3Q7TAAHc3VwcG9ydHQAD0xqYXZhL3V0aWwvU2V0O3hyACVhbmFseXNpcy5pY2ZnLlN1bW1hcnlTdGFjayRTdW1tYXJ5RW5kFZQmA8fWa+kCAAB4cHNyADdzcGVjLmN2bGFzdC5RdWFsaWZpZWRNZXRob2RTaWduYXR1cmUkUXVhbGlmaWVkTWV0aG9kU2lnGH1MtG0dbPUCAANMAAZwYXJhbXNxAH4AAkwAE3F1YWxpZmllZE1ldGhvZE5hbWV0AChMc3BlYy9jdmxhc3QvQ29udHJhY3RGdW5jdGlvbklkZW50aWZpZXI7TAADcmVzcQB+AAJ4cHNyABNqYXZhLnV0aWwuQXJyYXlMaXN0eIHSHZnHYZ0DAAFJAARzaXpleHAAAAABdwQAAAABc3IAGXNwZWMuY3ZsYXN0LlZNUGFyYW0kTmFtZWT9C66+edYZbAIABEwABG5hbWV0ABJMamF2YS9sYW5nL1N0cmluZztMAAxvcmlnaW5hbE5hbWVxAH4ADEwABXJhbmdldAAWTHNwZWMvY3ZsYXN0L0NWTFJhbmdlO0wABnZtVHlwZXQALkxzcGVjL2N2bGFzdC90eXBlZGVzY3JpcHRvcnMvVk1UeXBlRGVzY3JpcHRvcjt4cgATc3BlYy5jdmxhc3QuVk1QYXJhbXyNTHZusLGIAgAAeHB0AAFkcQB+ABFzcgAac3BlYy5jdmxhc3QuQ1ZMUmFuZ2UkRW1wdHkKQULasOXTrwIAAUwAB2NvbW1lbnRxAH4ADHhyABRzcGVjLmN2bGFzdC5DVkxSYW5nZRrNE9gkPkLmAgAAeHB0AABzcgAzc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkVWTVR5cGVEZXNjcmlwdG9yJFVJbnRLqHosSzB6DiUCAAFJAAhiaXR3aWR0aHhyAERzcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRVZNVHlwZURlc2NyaXB0b3IkRVZNSXNvbW9ycGhpY1ZhbHVlVHlwZZbjlXdq3fF/AgAAeHIAOnNwZWMuY3ZsYXN0LnR5cGVkZXNjcmlwdG9ycy5FVk1UeXBlRGVzY3JpcHRvciRFVk1WYWx1ZVR5cGUQ5NL1qK834QIAAHhyAC1zcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRVZNVHlwZURlc2NyaXB0b3JeVh3cxo4+6AIAAHhwAAABAHhzcgAdc3BlYy5jdmxhc3QuUXVhbGlmaWVkRnVuY3Rpb27lKUzy5DlRgwIAAkwABGhvc3R0AB5Mc3BlYy9jdmxhc3QvU29saWRpdHlDb250cmFjdDtMAAhtZXRob2RJZHEAfgAMeHBzcgAcc3BlYy5jdmxhc3QuU29saWRpdHlDb250cmFjdCNpfXcagT2iAgABTAAEbmFtZXEAfgAMeHB0AAxUZXN0Q29udHJhY3R0AAZkb3VibGVzcQB+AAkAAAABdwQAAAABc3IAG3NwZWMuY3ZsYXN0LlZNUGFyYW0kVW5uYW1lZAIPTbn85XVlAgACTAAFcmFuZ2VxAH4ADUwABnZtVHlwZXEAfgAOeHEAfgAPc3EAfgAScQB+ABVzcQB+ABYAAAEAeHNxAH4ACQAAAAF3BAAAAAFzcgAbYW5hbHlzaXMuaXAuSW50ZXJuYWxGdW5jUmV05InEVWrb2SYCAANJAAZvZmZzZXRMAAhsb2NhdGlvbnQAJ0xhbmFseXNpcy9pcC9JbnRlcm5hbEZ1bmNWYWx1ZUxvY2F0aW9uO0wAAXN0ABdMdmMvZGF0YS9UQUNTeW1ib2wkVmFyO3hwAAAAAHNyACxhbmFseXNpcy5pcC5JbnRlcm5hbEZ1bmNWYWx1ZUxvY2F0aW9uJFNjYWxhcurS/t67vyj1AgAAeHIAJWFuYWx5c2lzLmlwLkludGVybmFsRnVuY1ZhbHVlTG9jYXRpb25sjAqdSNnt+wIAAHhwc3IANXZjLmRhdGEuVEFDU3ltYm9sJFZhciRXaXRoRGVmYXVsdENhbGxJbmRleCRXaXRoQml0MjU2nq3gkxche2QCAAJMAARtZXRhdAAeTGNvbS9jZXJ0b3JhL2NvbGxlY3QvVHJlYXBNYXA7TAAKbmFtZVByZWZpeHEAfgAMeHIAFXZjLmRhdGEuVEFDU3ltYm9sJFZhcvxIa9S+MEYRAgAAeHIAEXZjLmRhdGEuVEFDU3ltYm9sE17/6RpKKNACAAB4cHNyACBjb20uY2VydG9yYS5jb2xsZWN0Lkhhc2hUcmVhcE1hcM4n+3qupXKcAgADTAADa2V5dAASTGphdmEvbGFuZy9PYmplY3Q7TAAEbmV4dHQAK0xjb20vY2VydG9yYS9jb2xsZWN0L0tleVZhbHVlUGFpckxpc3QkTW9yZTtMAAV2YWx1ZXEAfgA1eHIAJGNvbS5jZXJ0b3JhLmNvbGxlY3QuQWJzdHJhY3RUcmVhcE1hcC1u3UdoTQYZAgAAeHIAGWNvbS5jZXJ0b3JhLmNvbGxlY3QuVHJlYXD/3sPjttw/IwIAAkwABGxlZnR0ABtMY29tL2NlcnRvcmEvY29sbGVjdC9UcmVhcDtMAAVyaWdodHEAfgA5eHBzcQB+ADRwcHNyAAt0YWMuTWV0YUtleWr2F4pDsqLdAgADTAAPZXJhc3VyZVN0cmF0ZWd5dAAdTHRhYy9NZXRhS2V5JEVyYXN1cmVTdHJhdGVneTtMAARuYW1lcQB+AAxMAAN0eXB0ABFMamF2YS9sYW5nL0NsYXNzO3hwfnIAG3RhYy5NZXRhS2V5JEVyYXN1cmVTdHJhdGVneQAAAAAAAAAAEgAAeHIADmphdmEubGFuZy5FbnVtAAAAAAAAAAASAAB4cHQACUNhbm9uaWNhbHQAElRhYy5zeW1ib2wua2V5d29yZHZyACJ2Yy5kYXRhLlRBQ1N5bWJvbCRWYXIkS2V5d29yZEVudHJ5TuPA5DR23HYCAAB4cHBzcgAydmMuZGF0YS5UQUNTeW1ib2wkVmFyJEtleXdvcmRFbnRyeSRUQUNLZXl3b3JkRW50cnm4mRaPLAQsrQIAAkkAFm1heWJlVEFDS2V5d29yZE9yZGluYWxMAARuYW1lcQB+AAx4cQB+AEUAAAAtdAABTHBzcQB+ADxxAH4AQnQAEHRhYy5zdGFjay5oZWlnaHR2cgARamF2YS5sYW5nLkludGVnZXIS4qCk94GHOAIAAUkABXZhbHVleHIAEGphdmEubGFuZy5OdW1iZXKGrJUdC5TgiwIAAHhwcHNxAH4ATAAAA/90AANSNjl4c3IAImphdmEudXRpbC5Db2xsZWN0aW9ucyRTaW5nbGV0b25TZXQsUkGYKcCxvwIAAUwAB2VsZW1lbnRxAH4ANXhwcQB+ADM="}
		JumpCmd 9_0_0_5_0_0
	}
	Block 9_0_0_5_0_0 Succ [10_0_0_0_0_0] {
		AnnotationCmd:140 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":234,"bytecodeCount":8,"sources":[{"source":0,"begin":506,"end":923}]}}
		AnnotationCmd:138 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1180,"bytecodeCount":14,"sources":[{"source":1,"begin":957,"end":1179},{"source":1,"begin":1050,"end":1054},{"source":1,"begin":1088,"end":1090},{"source":1,"begin":1077,"end":1086},{"source":1,"begin":1073,"end":1091},{"source":1,"begin":1065,"end":1091},{"source":1,"begin":1101,"end":1172},{"source":1,"begin":1169,"end":1170},{"source":1,"begin":1158,"end":1167},{"source":1,"begin":1154,"end":1171},{"source":1,"begin":1145,"end":1151}]}}
		AnnotationCmd:138 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1165,"bytecodeCount":5,"sources":[{"source":1,"begin":833,"end":951},{"source":1,"begin":920,"end":944},{"source":1,"begin":938,"end":943}]}}
		AnnotationCmd:138 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1383,"bytecodeCount":9,"sources":[{"source":1,"begin":1850,"end":1927},{"source":1,"begin":1887,"end":1894},{"source":1,"begin":1916,"end":1921},{"source":1,"begin":1905,"end":1921},{"source":1,"begin":1895,"end":1927}]}}
		AnnotationCmd:138 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1174,"bytecodeCount":6,"sources":[{"source":1,"begin":920,"end":944},{"source":1,"begin":915,"end":918},{"source":1,"begin":908,"end":945},{"source":1,"begin":898,"end":951}]}}
		AnnotationCmd:122 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.EVMFunctionReturnWrite","returnbufOffset":"0","returnValueSym":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R69","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1023}]},"callIndex":5}}
		AnnotationCmd:138 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1201,"bytecodeCount":6,"sources":[{"source":1,"begin":1101,"end":1172},{"source":1,"begin":1055,"end":1179}]}}
		AnnotationCmd:138 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":247,"bytecodeCount":8,"sources":[{"source":0,"begin":506,"end":923}]}}
		AssignExpCmd:122 lastHasThrown!!70:42 false
		AssignExpCmd:122 lastReverted!!71:6 false
		AnnotationCmd:141 JSON{"key":{"name":"tac.return.path","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}
		AnnotationCmd:122 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.HaltSnippet.Return","range":{"specFile":"TestContract.sol","start":{"line":9,"charByteOffset":4},"end":{"line":11,"charByteOffset":5}}}}
		LabelCmd:122 "End procedure TestContract-double(uint256)"
		LabelCmd:122 "3: Move primitive value for variable r3361:int..."
		AssignExpCmd:122 CANON59!!72:17 R69:24
		LabelCmd:122 "...done 3"
		AnnotationCmd:122 JSON{"key":{"name":"call.trace.pop","type":"analysis.icfg.Inliner$CallStack$PopRecord","erasureStrategy":"Canonical"},"value":{"callee":{"contractId":"ce4604a0000000000000000000000001","sigHash":{"n":"eee97206"},"attr":{"#class":"scene.MethodAttribute.Common"}},"calleeId":5}}
	}
	Block 10_0_0_0_0_0 Succ [11_0_0_7_0_0] {
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageGlobalChangeSnippet.StorageTakeSnapshot","lhs":{"namePrefix":"lastStorage","tag":{"#class":"tac.Tag.BlockchainState"},"callIndex":0,"meta":[{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule"}},{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry","name":"lastStorage"}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.VMInternal.BlockchainState"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"lastStorage"}]}}}
		AnnotationCmd:122 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":28}
		AnnotationCmd:142 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Definition","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":38,"charByteOffset":4},"end":{"line":38,"charByteOffset":26}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"idL":[{"#class":"spec.cvlast.CVLLhs.Id","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":38,"charByteOffset":4},"end":{"line":38,"charByteOffset":14}},"id":"r4","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":38,"charByteOffset":4},"end":{"line":38,"charByteOffset":14}}}}],"exp":{"#class":"spec.cvlast.CVLExp.ApplyExp.ContractFunction.Concrete","methodIdWithCallContext":{"#class":"spec.cvlast.ConcreteMethod","signature":{"#class":"spec.cvlast.ExternalQualifiedMethodSignature.ExternalQualifiedMethodSig","wrapped":{"#class":"spec.cvlast.QualifiedMethodSignature.QualifiedMethodSig","qualifiedMethodName":{"#class":"spec.cvlast.QualifiedFunction","host":{"name":"TestContract"},"methodId":"getval"},"params":[],"res":[{"#class":"spec.cvlast.VMParam.Unnamed","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}}]},"sighashInt":{"n":"31b6bd06"}}},"args":[],"noRevert":true,"storage":{"id":"lastStorage","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.VMInternal.BlockchainState"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Empty","comment":"empty storage type"}},"twoStateIndex":"NEITHER"},"isWhole":false,"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.ReturnValue"}},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":38,"charByteOffset":17},"end":{"line":38,"charByteOffset":25}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.CallResolution$DirectPassing","target":{"methodSignature":{"#class":"spec.cvlast.ExternalQualifiedMethodSignature.ExternalQualifiedMethodSig","wrapped":{"#class":"spec.cvlast.QualifiedMethodSignature.QualifiedMethodSig","qualifiedMethodName":{"#class":"spec.cvlast.QualifiedFunction","host":{"name":"TestContract"},"methodId":"getval"},"params":[],"res":[{"#class":"spec.cvlast.VMParam.Unnamed","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}}]},"sighashInt":{"n":"31b6bd06"}},"definitelyNonPayable":true,"annotation":{"visibility":"EXTERNAL","envFree":true,"library":false,"virtual":false},"stateMutability":"nonpayable","evmExternalMethodInfo":{"sigHash":"31b6bd06","name":"getval","argTypes":[],"resultTypes":[{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}],"stateMutability":"nonpayable","isConstant":false,"isLibrary":false,"contractName":"TestContract","contractInstanceId":"ce4604a0000000000000000000000001","sourceSegment":{"range":{"specFile":"TestContract.sol","start":{"line":13,"charByteOffset":4},"end":{"line":15,"charByteOffset":5}},"content":"function getval() public returns (uint256) {\n        return val;\n    }"}}},"hasEnv":false}}},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
	}
	Block 11_0_0_7_0_0 Succ [12_0_0_0_0_0] {
		AssignHavocCmd:143 CANON85!!73:4
		AnnotationCmd:143 JSON{"key":{"name":"call.trace.push","type":"analysis.icfg.Inliner$CallStack$PushRecord","erasureStrategy":"Canonical"},"value":{"callee":{"contractId":"ce4604a0000000000000000000000001","sigHash":{"n":"31b6bd06"},"attr":{"#class":"scene.MethodAttribute.Common"}},"summary":null,"convention":{"#class":"analysis.icfg.Inliner.CallConventionType.FromCVL"},"calleeId":7}}
		AssignHavocCmd:143 tacCalldatasize!!74:9
		AssumeExpCmd Eq(tacCalldatasize!!74:9 0x4 )
		AssignExpCmd:143 tacCalldatabuf@7:16 MapDefinition(CANON86:bv256 -> Ite(Lt(CANON86 tacCalldatasize!!74:9 ) Select(Select(Select(CANON28!7:25 CANON86 ) tacCalldatasize!!74:9 ) 0x31b6bd06 ) 0x0 ) bytemap)
		AssignExpCmd:143 R75:20 Select(Select(Select(CANON28!7:25 0x0 ) 0x4 ) 0x31b6bd06 )
		AssumeExpCmd LAnd(Ge(R75:20 0x31b6bd0600000000000000000000000000000000000000000000000000000000 ) Le(R75:20 0x31b6bd06ffffffffffffffffffffffffffffffffffffffffffffffffffffffff ) )
		AnnotationCmd:143 JSON{"key":{"name":"cvl.arg-serialization.start","type":"spec.CVLInvocationCompiler$StartSerializationMarker","erasureStrategy":"Canonical"},"value":{"id":2,"callId":7}}
		AnnotationCmd:143 JSON{"key":{"name":"cvl.arg-serialization.end","type":"spec.CVLInvocationCompiler$EndSerializationMarker","erasureStrategy":"Canonical"},"value":{"id":2,"callId":7}}
		LabelCmd:143 "Start procedure TestContract-getval()"
		AnnotationCmd:143 JSON{"key":{"name":"fps.free-pointer-is-scalarized","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true}
		AssignExpCmd:143 R77:20 Select(tacExtcodesize!!4:7 Apply(to_skey:bif R12:109) )
		AssumeExpCmd Ge(R77:20 0x1 )
		AnnotationCmd:143 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.RawStorageAccess.WithLocSym","isLoad":true,"loc":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R12","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"tacAddress","maybeTACKeywordOrdinal":22}},{"key":{"name":"tac.env.known-bit-width","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":160},{"key":{"name":"tac.contract.sym.addr.name","type":"java.lang.String","erasureStrategy":"Erased"},"value":"TestContract"},{"key":{"name":"tac.contract.sym.addr","type":"java.math.BigInteger","erasureStrategy":"Erased"},"value":"ce4604a0000000000000000000000001"}]},"contractInstance":"ce4604a0000000000000000000000001","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R77","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"storageType":null,"range":null}}
		AnnotationCmd:143 JSON{"key":{"name":"internal.func.finder.info","type":"analysis.ip.InternalFunctionFinderReport","erasureStrategy":"Erased"},"value":{"unresolvedFunctions":[]}}
		AnnotationCmd:143 JSON{"key":{"name":"fps.free-pointer-is-scalarized","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true}
		AnnotationCmd:143 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":0,"bytecodeCount":8,"sources":[{"source":0,"begin":25,"end":2021}]}}
		LabelCmd "→ Assuming FP is strictly monotonic increasing"
		LabelCmd "←"
		AnnotationCmd:143 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.StartBranchSnippet","branchIndex":4,"branchSource":{"range":{"specFile":"TestContract.sol","start":{"line":2,"charByteOffset":0},"end":{"line":24,"charByteOffset":1}},"content":"contract TestContract {...}"}}}
		AnnotationCmd:143 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.EndBranchSnippet","branchIndex":4}}
		AnnotationCmd:144 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":16,"bytecodeCount":7,"sources":[{"source":0,"begin":25,"end":2021}]}}
		AnnotationCmd:144 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":26,"bytecodeCount":9,"sources":[{"source":0,"begin":25,"end":2021}]}}
		AnnotationCmd:144 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":92,"bytecodeCount":4,"sources":[{"source":0,"begin":929,"end":1257}]}}
		AnnotationCmd:143 JSON{"key":{"name":"internal.func.start","type":"analysis.ip.InternalFuncStartAnnotation","erasureStrategy":"CallTrace"},"value":{"id":0,"startPc":256,"args":[],"methodSignature":{"#class":"spec.cvlast.QualifiedMethodSignature.QualifiedMethodSig","qualifiedMethodName":{"#class":"spec.cvlast.QualifiedFunction","host":{"name":"TestContract"},"methodId":"getval"},"params":[],"res":[{"#class":"spec.cvlast.VMParam.Unnamed","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}}]},"stackOffsetToArgPos":{},"callSiteSrc":{"source":0,"begin":929,"len":328,"jumpType":"ENTER","address":"ce4604a0000000000000000000000001","sourceContext":{"indexToFilePath":{"0":"TestContract.sol"},"sourceDir":".post_autofinders.0"}}}}
		AnnotationCmd:145 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":256,"bytecodeCount":17,"sources":[{"source":0,"begin":929,"end":1257},{"source":0,"begin":963,"end":970},{"source":0,"begin":1059,"end":1072},{"source":0,"begin":991,"end":1057},{"source":0,"begin":984,"end":1073},{"source":0,"begin":1149,"end":1150},{"source":0,"begin":1081,"end":1147},{"source":0,"begin":1074,"end":1151},{"source":0,"begin":1227,"end":1228},{"source":0,"begin":1159,"end":1225},{"source":0,"begin":1152,"end":1229},{"source":0,"begin":1247,"end":1250},{"source":0,"begin":1240,"end":1250}]}}
		AnnotationCmd:146 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.ApplyHook","hookPatternString":"Hook Sload uint256 contractVal 0x0.0x0 tacS","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":15,"charByteOffset":0},"end":{"line":18,"charByteOffset":1}}}}
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.InlinedHook","cvlPattern":{"#class":"spec.cvlast.CVLHookPattern.StoragePattern.Load","value":{"name":"contractVal","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":15,"charByteOffset":11},"end":{"line":15,"charByteOffset":30}}},"slot":{"#class":"spec.cvlast.CVLSlotPattern.Static.Named","solidityContract":{"name":"TestContract"},"name":"val"},"base":"STORAGE"},"substitutions":[{"name":"contractVal","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":15,"charByteOffset":11},"end":{"line":15,"charByteOffset":30}}},{"#class":"vc.data.HookValue.Direct","expr":{"#class":"vc.data.TACExpr.Sym.Var","s":{"namePrefix":"R6","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1021}]},"tag":{"#class":"tac.Tag.Bit256"}}}],"displayPath":null}}
		AssignExpCmd:147 B79:12 true
		AssignExpCmd:148 B80 true
		AssignExpCmd:149 I81 CANON92:41
		AnnotationCmd:150 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.GhostRead","readValue":{"namePrefix":"CANON92","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.ghost","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"innerVal"}]},"indices":[],"name":"innerVal","sort":{"#class":"spec.cvlast.GhostSort.Variable"},"persistent":false,"range":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":17,"charByteOffset":12},"end":{"line":17,"charByteOffset":20}},"readExpr":"innerVal"}}
		AssignExpCmd:151 CANON94:11 Eq(I81 CANON88!!8:8 )
		AssumeCmd CANON94:11
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":30}
		AnnotationCmd:143 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"CANON88!!8","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.storage.non-indexed-path.family","type":"analysis.storage.StorageAnalysisResult$StoragePaths","erasureStrategy":"Canonical"},"value":{"storagePaths":[{"#class":"analysis.storage.StorageAnalysisResult.NonIndexedPath.Root","slot":"0"}]}},{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.scalarization.sort","type":"vc.data.ScalarizationSort","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.ScalarizationSort.Split","idx":"0"}},{"key":{"name":"tac.storage.bit-width","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":256},{"key":{"name":"tac.storage.pretty.paths","type":"analysis.storage.DisplayPaths","erasureStrategy":"Erased"},"value":{"paths":[{"#class":"analysis.storage.DisplayPath.Root","name":"val"}]}},{"key":{"name":"tac.slot.type","type":"spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType","erasureStrategy":"Canonical"},"value":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"key":{"name":"tac.storage.non-indexed-path","type":"analysis.storage.StorageAnalysisResult$NonIndexedPath","erasureStrategy":"Canonical"},"value":{"#class":"analysis.storage.StorageAnalysisResult.NonIndexedPath.Root","slot":"0"}},{"key":{"name":"tac.storage","type":"java.math.BigInteger","erasureStrategy":"Canonical"},"value":"ce4604a0000000000000000000000001"},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1021}]},"displayPath":{"#class":"analysis.storage.DisplayPath.Root","name":"val"},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":14,"charByteOffset":15},"end":{"line":14,"charByteOffset":18}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.Id","id":0}}}
		AnnotationCmd:143 JSON{"key":{"name":"internal.func.end","type":"analysis.ip.InternalFuncExitAnnotation","erasureStrategy":"Canonical"},"value":{"id":0,"rets":[{"s":{"namePrefix":"CANON88!!8","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.storage.non-indexed-path.family","type":"analysis.storage.StorageAnalysisResult$StoragePaths","erasureStrategy":"Canonical"},"value":{"storagePaths":[{"#class":"analysis.storage.StorageAnalysisResult.NonIndexedPath.Root","slot":"0"}]}},{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.scalarization.sort","type":"vc.data.ScalarizationSort","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.ScalarizationSort.Split","idx":"0"}},{"key":{"name":"tac.storage.bit-width","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":256},{"key":{"name":"tac.storage.pretty.paths","type":"analysis.storage.DisplayPaths","erasureStrategy":"Erased"},"value":{"paths":[{"#class":"analysis.storage.DisplayPath.Root","name":"val"}]}},{"key":{"name":"tac.slot.type","type":"spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType","erasureStrategy":"Canonical"},"value":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"key":{"name":"tac.storage.non-indexed-path","type":"analysis.storage.StorageAnalysisResult$NonIndexedPath","erasureStrategy":"Canonical"},"value":{"#class":"analysis.storage.StorageAnalysisResult.NonIndexedPath.Root","slot":"0"}},{"key":{"name":"tac.storage","type":"java.math.BigInteger","erasureStrategy":"Canonical"},"value":"ce4604a0000000000000000000000001"},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1023}]},"offset":0,"location":{"#class":"analysis.ip.InternalFuncValueLocation.Scalar"}}],"methodSignature":{"#class":"spec.cvlast.QualifiedMethodSignature.QualifiedMethodSig","qualifiedMethodName":{"#class":"spec.cvlast.QualifiedFunction","host":{"name":"TestContract"},"methodId":"getval"},"params":[],"res":[{"#class":"spec.cvlast.VMParam.Unnamed","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"spec.cvlast.CVLRange.Empty"}}]}}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":100,"bytecodeCount":8,"sources":[{"source":0,"begin":929,"end":1257}]}}
		AnnotationCmd:145 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1180,"bytecodeCount":14,"sources":[{"source":1,"begin":957,"end":1179},{"source":1,"begin":1050,"end":1054},{"source":1,"begin":1088,"end":1090},{"source":1,"begin":1077,"end":1086},{"source":1,"begin":1073,"end":1091},{"source":1,"begin":1065,"end":1091},{"source":1,"begin":1101,"end":1172},{"source":1,"begin":1169,"end":1170},{"source":1,"begin":1158,"end":1167},{"source":1,"begin":1154,"end":1171},{"source":1,"begin":1145,"end":1151}]}}
		AnnotationCmd:145 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1165,"bytecodeCount":5,"sources":[{"source":1,"begin":833,"end":951},{"source":1,"begin":920,"end":944},{"source":1,"begin":938,"end":943}]}}
		AnnotationCmd:145 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1383,"bytecodeCount":9,"sources":[{"source":1,"begin":1850,"end":1927},{"source":1,"begin":1887,"end":1894},{"source":1,"begin":1916,"end":1921},{"source":1,"begin":1905,"end":1921},{"source":1,"begin":1895,"end":1927}]}}
		AnnotationCmd:145 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1174,"bytecodeCount":6,"sources":[{"source":1,"begin":920,"end":944},{"source":1,"begin":915,"end":918},{"source":1,"begin":908,"end":945},{"source":1,"begin":898,"end":951}]}}
		AnnotationCmd:143 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.EVMFunctionReturnWrite","returnbufOffset":"0","returnValueSym":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"CANON88!!8","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.storage.non-indexed-path.family","type":"analysis.storage.StorageAnalysisResult$StoragePaths","erasureStrategy":"Canonical"},"value":{"storagePaths":[{"#class":"analysis.storage.StorageAnalysisResult.NonIndexedPath.Root","slot":"0"}]}},{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.scalarization.sort","type":"vc.data.ScalarizationSort","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.ScalarizationSort.Split","idx":"0"}},{"key":{"name":"tac.storage.bit-width","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":256},{"key":{"name":"tac.storage.pretty.paths","type":"analysis.storage.DisplayPaths","erasureStrategy":"Erased"},"value":{"paths":[{"#class":"analysis.storage.DisplayPath.Root","name":"val"}]}},{"key":{"name":"tac.slot.type","type":"spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType","erasureStrategy":"Canonical"},"value":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"key":{"name":"tac.storage.non-indexed-path","type":"analysis.storage.StorageAnalysisResult$NonIndexedPath","erasureStrategy":"Canonical"},"value":{"#class":"analysis.storage.StorageAnalysisResult.NonIndexedPath.Root","slot":"0"}},{"key":{"name":"tac.storage","type":"java.math.BigInteger","erasureStrategy":"Canonical"},"value":"ce4604a0000000000000000000000001"},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1023}]},"callIndex":7}}
		AnnotationCmd:145 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":1201,"bytecodeCount":6,"sources":[{"source":1,"begin":1101,"end":1172},{"source":1,"begin":1055,"end":1179}]}}
		AnnotationCmd:145 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"da560ac15b509fa81ecdbfe8703fc549973862a6c99487cf19bea297e2ef30da","pc":113,"bytecodeCount":8,"sources":[{"source":0,"begin":929,"end":1257}]}}
		AssignExpCmd:143 lastHasThrown!!83:42 false
		AssignExpCmd:143 lastReverted!!84:6 false
		AnnotationCmd:153 JSON{"key":{"name":"tac.return.path","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}
		AnnotationCmd:143 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.HaltSnippet.Return","range":{"specFile":"TestContract.sol","start":{"line":13,"charByteOffset":4},"end":{"line":15,"charByteOffset":5}}}}
		LabelCmd:143 "End procedure TestContract-getval()"
		LabelCmd:143 "5: Move primitive value for variable r4467:int..."
		AssignExpCmd:143 CANON85!!85:4 CANON88!!8:8
		LabelCmd:143 "...done 5"
		AnnotationCmd:143 JSON{"key":{"name":"call.trace.pop","type":"analysis.icfg.Inliner$CallStack$PopRecord","erasureStrategy":"Canonical"},"value":{"callee":{"contractId":"ce4604a0000000000000000000000001","sigHash":{"n":"31b6bd06"},"attr":{"#class":"scene.MethodAttribute.Common"}},"calleeId":7}}
	}
	Block 12_0_0_0_0_0 Succ [] {
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageGlobalChangeSnippet.StorageTakeSnapshot","lhs":{"namePrefix":"lastStorage","tag":{"#class":"tac.Tag.BlockchainState"},"callIndex":0,"meta":[{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule"}},{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry","name":"lastStorage"}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.VMInternal.BlockchainState"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"lastStorage"}]}}}
		AnnotationCmd:143 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":29}
		AnnotationCmd:154 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.AssumeCmd.Assume","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":39,"charByteOffset":4},"end":{"line":39,"charByteOffset":20}},"exp":{"#class":"spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp","l":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"t","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":39,"charByteOffset":12},"end":{"line":39,"charByteOffset":13}}},"twoStateIndex":"NEITHER"},"r":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"num","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":39,"charByteOffset":16},"end":{"line":39,"charByteOffset":19}}},"twoStateIndex":"NEITHER"},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":39,"charByteOffset":12},"end":{"line":39,"charByteOffset":19}}}},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AssignExpCmd:155 I86 0x14(int)
		AssignExpCmd:156 I87 0x5(int)
		AssignExpCmd:157 B88 true
		AnnotationCmd:158 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":31}
		AnnotationCmd:159 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.AssumeCmd.Assume","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":40,"charByteOffset":4},"end":{"line":40,"charByteOffset":20}},"exp":{"#class":"spec.cvlast.CVLExp.RelopExp.EqExp","l":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"t","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":40,"charByteOffset":12},"end":{"line":40,"charByteOffset":13}}},"twoStateIndex":"NEITHER"},"r":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"r1","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":40,"charByteOffset":17},"end":{"line":40,"charByteOffset":19}}},"twoStateIndex":"NEITHER"},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":40,"charByteOffset":12},"end":{"line":40,"charByteOffset":19}}}},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AssignExpCmd:160 I89 0x14(int)
		AssignExpCmd:161 I90 0x14(int)
		AssignExpCmd:162 CANON100:11 true
		AnnotationCmd:163 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":32}
		AnnotationCmd:164 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Assert","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":41,"charByteOffset":4},"end":{"line":41,"charByteOffset":19}},"exp":{"#class":"spec.cvlast.CVLExp.RelopExp.EqExp","l":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"r2","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":41,"charByteOffset":11},"end":{"line":41,"charByteOffset":13}}},"twoStateIndex":"NEITHER"},"r":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"9","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"9"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":41,"charByteOffset":17},"end":{"line":41,"charByteOffset":18}}}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":41,"charByteOffset":11},"end":{"line":41,"charByteOffset":18}}}},"description":"r2 == 9","scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AssignExpCmd:165 I91 0x9
		AssignExpCmd:166 I92 0x9
		AssignExpCmd:167 CANON103:11 true
		AssertCmd:168 true "r2 == 9"
		AnnotationCmd:169 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":33}
		AnnotationCmd:170 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Assert","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":42,"charByteOffset":4},"end":{"line":42,"charByteOffset":20}},"exp":{"#class":"spec.cvlast.CVLExp.RelopExp.EqExp","l":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"r3","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":42,"charByteOffset":11},"end":{"line":42,"charByteOffset":13}}},"twoStateIndex":"NEITHER"},"r":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"e","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"e"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":42,"charByteOffset":17},"end":{"line":42,"charByteOffset":19}}}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":42,"charByteOffset":11},"end":{"line":42,"charByteOffset":19}}}},"description":"r3 == 14","scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AssignExpCmd:171 I93 CANON59!!72:17
		AssignExpCmd:172 I94 0xe
		AssignExpCmd:173 CANON106!!95:11 Eq(I93 0xe(int) )
		AssertCmd:174 CANON106!!95:11 "r3 == 14"
		AnnotationCmd:175 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":34}
		AnnotationCmd:176 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Assert","cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":43,"charByteOffset":4},"end":{"line":43,"charByteOffset":19}},"exp":{"#class":"spec.cvlast.CVLExp.RelopExp.EqExp","l":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"r4","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":43,"charByteOffset":11},"end":{"line":43,"charByteOffset":13}}},"twoStateIndex":"NEITHER"},"r":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"1","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"1"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":43,"charByteOffset":17},"end":{"line":43,"charByteOffset":18}}}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"},"cvlRange":{"#class":"spec.cvlast.CVLRange.Range","specFile":"Basic.spec","start":{"line":43,"charByteOffset":11},"end":{"line":43,"charByteOffset":18}}}},"description":"r4 == 1","scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":2}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AssignExpCmd:177 I96 CANON85!!85:4
		AssignExpCmd:178 B97:12 true
		AssignExpCmd:179 CANON109:11 false
		AssertCmd:180 false "r4 == 1"
	}
}
Axioms {
}
Metas {
  "0": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacM0x40",
        "maybeTACKeywordOrdinal": 39
      }
    },
    {
      "key": {
        "name": "tac.is.reserved.memory.slot.var",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "40"
    }
  ],
  "1": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCodesize",
        "maybeTACKeywordOrdinal": 7
      }
    },
    {
      "key": {
        "name": "tac.codesize",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    },
    {
      "key": {
        "name": "tac.no.callindex",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "2": [
    {
      "key": {
        "name": "tac.immutable.array",
        "type": "vc.data.ImmutableBound",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "sym": {
          "#class": "vc.data.TACSymbol.Var.Full",
          "namePrefix": "tacCalldatasize",
          "tag": {
            "#class": "tac.Tag.Bit256"
          },
          "callIndex": 0,
          "meta": [
            {
              "key": {
                "name": "Tac.symbol.keyword",
                "type": "vc.data.TACSymbol$Var$KeywordEntry",
                "erasureStrategy": "Canonical"
              },
              "value": {
                "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                "name": "tacCalldatasize",
                "maybeTACKeywordOrdinal": 12
              }
            }
          ]
        }
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCalldatabuf",
        "maybeTACKeywordOrdinal": 15
      }
    },
    {
      "key": {
        "name": "tac.wordmap-key",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "4"
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Split",
        "idx": "4"
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 256
    },
    {
      "key": {
        "name": "tac.calldata.offset",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "4"
    },
    {
      "key": {
        "name": "tac.is.calldata",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "3": [
    {
      "key": {
        "name": "tac.immutable.array",
        "type": "vc.data.ImmutableBound",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "sym": {
          "#class": "vc.data.TACSymbol.Var.Full",
          "namePrefix": "tacCalldatasize",
          "tag": {
            "#class": "tac.Tag.Bit256"
          },
          "callIndex": 0,
          "meta": [
            {
              "key": {
                "name": "Tac.symbol.keyword",
                "type": "vc.data.TACSymbol$Var$KeywordEntry",
                "erasureStrategy": "Canonical"
              },
              "value": {
                "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                "name": "tacCalldatasize",
                "maybeTACKeywordOrdinal": 12
              }
            }
          ]
        }
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCalldatabuf",
        "maybeTACKeywordOrdinal": 15
      }
    },
    {
      "key": {
        "name": "tac.wordmap-key",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "24"
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Split",
        "idx": "24"
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 256
    },
    {
      "key": {
        "name": "tac.calldata.offset",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "24"
    },
    {
      "key": {
        "name": "tac.is.calldata",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "4": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 38,
            "charByteOffset": 4
          },
          "end": {
            "line": 38,
            "charByteOffset": 14
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "r4"
    }
  ],
  "5": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacAddress",
        "maybeTACKeywordOrdinal": 22
      }
    },
    {
      "key": {
        "name": "tac.env.known-bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 160
    }
  ],
  "6": [
    {
      "key": {
        "name": "tac.last.reverted",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule"
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "lastReverted"
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "lastReverted"
    }
  ],
  "7": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacExtcodesize",
        "maybeTACKeywordOrdinal": 25
      }
    },
    {
      "key": {
        "name": "tac.no.callindex",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.is.extcodesize",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "8": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Split",
        "idx": "0"
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 256
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.Root",
            "name": "val"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
        "bitwidth": 256
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
        "slot": "0"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "9": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCalldatasize",
        "maybeTACKeywordOrdinal": 12
      }
    }
  ],
  "10": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule"
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "calledContract"
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "calledContract"
    }
  ],
  "11": [
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    }
  ],
  "12": [
    {
      "key": {
        "name": "tac.was.replaced.with.bool",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "13": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacBalance",
        "maybeTACKeywordOrdinal": 23
      }
    },
    {
      "key": {
        "name": "tac.no.callindex",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "14": [
    {
      "key": {
        "name": "tac.immutable.array",
        "type": "vc.data.ImmutableBound",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "sym": {
          "#class": "vc.data.TACSymbol.Var.Full",
          "namePrefix": "tacCalldatasize",
          "tag": {
            "#class": "tac.Tag.Bit256"
          },
          "callIndex": 2,
          "meta": [
            {
              "key": {
                "name": "Tac.symbol.keyword",
                "type": "vc.data.TACSymbol$Var$KeywordEntry",
                "erasureStrategy": "Canonical"
              },
              "value": {
                "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                "name": "tacCalldatasize",
                "maybeTACKeywordOrdinal": 12
              }
            }
          ]
        }
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCalldatabuf",
        "maybeTACKeywordOrdinal": 15
      }
    },
    {
      "key": {
        "name": "tac.is.calldata",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "15": [
    {
      "key": {
        "name": "tac.immutable.array",
        "type": "vc.data.ImmutableBound",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "sym": {
          "#class": "vc.data.TACSymbol.Var.Full",
          "namePrefix": "tacCalldatasize",
          "tag": {
            "#class": "tac.Tag.Bit256"
          },
          "callIndex": 5,
          "meta": [
            {
              "key": {
                "name": "Tac.symbol.keyword",
                "type": "vc.data.TACSymbol$Var$KeywordEntry",
                "erasureStrategy": "Canonical"
              },
              "value": {
                "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                "name": "tacCalldatasize",
                "maybeTACKeywordOrdinal": 12
              }
            }
          ]
        }
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCalldatabuf",
        "maybeTACKeywordOrdinal": 15
      }
    },
    {
      "key": {
        "name": "tac.is.calldata",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "16": [
    {
      "key": {
        "name": "tac.immutable.array",
        "type": "vc.data.ImmutableBound",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "sym": {
          "#class": "vc.data.TACSymbol.Var.Full",
          "namePrefix": "tacCalldatasize",
          "tag": {
            "#class": "tac.Tag.Bit256"
          },
          "callIndex": 7,
          "meta": [
            {
              "key": {
                "name": "Tac.symbol.keyword",
                "type": "vc.data.TACSymbol$Var$KeywordEntry",
                "erasureStrategy": "Canonical"
              },
              "value": {
                "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                "name": "tacCalldatasize",
                "maybeTACKeywordOrdinal": 12
              }
            }
          ]
        }
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCalldatabuf",
        "maybeTACKeywordOrdinal": 15
      }
    },
    {
      "key": {
        "name": "tac.is.calldata",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "17": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 37,
            "charByteOffset": 4
          },
          "end": {
            "line": 37,
            "charByteOffset": 14
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "r3"
    }
  ],
  "18": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1021
    }
  ],
  "19": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "tacContractAt"
      }
    },
    {
      "key": {
        "name": "tac.contract.sym.addr.name",
        "type": "java.lang.String",
        "erasureStrategy": "Erased"
      },
      "value": "ecrecover"
    },
    {
      "key": {
        "name": "tac.contract.sym.addr",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Erased"
      },
      "value": "1"
    }
  ],
  "20": [
    {
      "key": {
        "name": "tac.is-temp-var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "21": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "tacContractAt"
      }
    },
    {
      "key": {
        "name": "tac.contract.sym.addr.name",
        "type": "java.lang.String",
        "erasureStrategy": "Erased"
      },
      "value": "sha256"
    },
    {
      "key": {
        "name": "tac.contract.sym.addr",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Erased"
      },
      "value": "2"
    }
  ],
  "22": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "tacContractAt"
      }
    },
    {
      "key": {
        "name": "tac.contract.sym.addr.name",
        "type": "java.lang.String",
        "erasureStrategy": "Erased"
      },
      "value": "identity"
    },
    {
      "key": {
        "name": "tac.contract.sym.addr",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Erased"
      },
      "value": "4"
    }
  ],
  "23": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "tacContractAt"
      }
    },
    {
      "key": {
        "name": "tac.contract.sym.addr.name",
        "type": "java.lang.String",
        "erasureStrategy": "Erased"
      },
      "value": "TestContract"
    },
    {
      "key": {
        "name": "tac.contract.sym.addr",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Erased"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "24": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1023
    }
  ],
  "25": [
    {
      "key": {
        "name": "tac.no.callindex",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "26": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "difficulty",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 32,
            "charByteOffset": 4
          },
          "end": {
            "line": 32,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.difficulty"
    }
  ],
  "27": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "gaslimit",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 32,
            "charByteOffset": 4
          },
          "end": {
            "line": 32,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.gaslimit"
    }
  ],
  "28": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "number",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 32,
            "charByteOffset": 4
          },
          "end": {
            "line": 32,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.number"
    }
  ],
  "29": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "timestamp",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 32,
            "charByteOffset": 4
          },
          "end": {
            "line": 32,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.timestamp"
    }
  ],
  "30": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 33,
            "charByteOffset": 4
          },
          "end": {
            "line": 33,
            "charByteOffset": 15
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "num"
    }
  ],
  "31": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 34,
            "charByteOffset": 4
          },
          "end": {
            "line": 34,
            "charByteOffset": 14
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "t"
    }
  ],
  "32": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 25,
            "charByteOffset": 4
          },
          "end": {
            "line": 25,
            "charByteOffset": 15
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "num"
    }
  ],
  "33": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 26,
            "charByteOffset": 4
          },
          "end": {
            "line": 26,
            "charByteOffset": 15
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "ret"
    }
  ],
  "34": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 35,
            "charByteOffset": 4
          },
          "end": {
            "line": 35,
            "charByteOffset": 14
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "r1"
    }
  ],
  "35": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 36,
            "charByteOffset": 4
          },
          "end": {
            "line": 36,
            "charByteOffset": 14
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "r2"
    }
  ],
  "36": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 11,
            "charByteOffset": 17
          },
          "end": {
            "line": 11,
            "charByteOffset": 26
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "a"
    }
  ],
  "37": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 11,
            "charByteOffset": 28
          },
          "end": {
            "line": 11,
            "charByteOffset": 37
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "b"
    }
  ],
  "38": [
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    }
  ],
  "39": [
    {
      "key": {
        "name": "cvl.ghost",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    }
  ],
  "40": [
    {
      "key": {
        "name": "cvl.ghost",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Ghost.Mapping",
        "key": {
          "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
          "k": 256
        },
        "value": {
          "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
          "k": 256
        }
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "ghost_double"
    }
  ],
  "41": [
    {
      "key": {
        "name": "cvl.ghost",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "innerVal"
    }
  ],
  "42": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule"
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "lastHasThrown"
      }
    },
    {
      "key": {
        "name": "tac.last.has.thrown",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "lastHasThrown"
    }
  ],
  "43": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "msg",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "msg",
              "fields": [
                {
                  "fieldName": "sender",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "value",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "sender",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 32,
            "charByteOffset": 4
          },
          "end": {
            "line": 32,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.msg.sender"
    }
  ],
  "44": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "msg",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "msg",
              "fields": [
                {
                  "fieldName": "sender",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "value",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "value",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 32,
            "charByteOffset": 4
          },
          "end": {
            "line": 32,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.msg.value"
    }
  ],
  "45": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "tx",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "tx",
              "fields": [
                {
                  "fieldName": "origin",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "origin",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 32,
            "charByteOffset": 4
          },
          "end": {
            "line": 32,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.tx.origin"
    }
  ],
  "46": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "basefee",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 32,
            "charByteOffset": 4
          },
          "end": {
            "line": 32,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.basefee"
    }
  ],
  "47": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "blobbasefee",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 32,
            "charByteOffset": 4
          },
          "end": {
            "line": 32,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.blobbasefee"
    }
  ],
  "48": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "coinbase",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "spec.cvlast.CVLRange.Range",
          "specFile": "Basic.spec",
          "start": {
            "line": 32,
            "charByteOffset": 4
          },
          "end": {
            "line": 32,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.coinbase"
    }
  ],
  "49": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacSighash",
        "maybeTACKeywordOrdinal": 6
      }
    }
  ],
  "50": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 0
    }
  ],
  "51": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1
    }
  ],
  "52": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 2
    }
  ],
  "53": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 3
    }
  ],
  "54": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 4
    }
  ],
  "55": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 5
    }
  ],
  "56": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 6
    }
  ],
  "57": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 7
    }
  ],
  "58": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 8
    }
  ],
  "59": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 9
    }
  ],
  "60": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 10
    }
  ],
  "61": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 11
    }
  ],
  "62": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 12
    }
  ],
  "63": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 13
    }
  ],
  "64": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 14
    }
  ],
  "65": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 15
    }
  ],
  "66": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 16
    }
  ],
  "67": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 17
    }
  ],
  "68": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 32,
          "charByteOffset": 4
        },
        "end": {
          "line": 32,
          "charByteOffset": 10
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 18
    }
  ],
  "69": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 32,
          "charByteOffset": 4
        },
        "end": {
          "line": 32,
          "charByteOffset": 10
        }
      }
    }
  ],
  "70": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 33,
          "charByteOffset": 4
        },
        "end": {
          "line": 33,
          "charByteOffset": 20
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 19
    }
  ],
  "71": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "5",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "5"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 33,
                "charByteOffset": 18
              },
              "end": {
                "line": 33,
                "charByteOffset": 19
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 33,
          "charByteOffset": 4
        },
        "end": {
          "line": 33,
          "charByteOffset": 20
        }
      }
    }
  ],
  "72": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 33,
          "charByteOffset": 4
        },
        "end": {
          "line": 33,
          "charByteOffset": 20
        }
      }
    }
  ],
  "73": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 34,
          "charByteOffset": 4
        },
        "end": {
          "line": 34,
          "charByteOffset": 14
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 20
    }
  ],
  "74": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 34,
          "charByteOffset": 4
        },
        "end": {
          "line": 34,
          "charByteOffset": 14
        }
      }
    }
  ],
  "75": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 35,
          "charByteOffset": 4
        },
        "end": {
          "line": 35,
          "charByteOffset": 24
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 21
    }
  ],
  "76": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 35,
          "charByteOffset": 4
        },
        "end": {
          "line": 35,
          "charByteOffset": 24
        }
      }
    }
  ],
  "77": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 25,
          "charByteOffset": 4
        },
        "end": {
          "line": 25,
          "charByteOffset": 21
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 22
    }
  ],
  "78": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "a",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 4
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "a"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 25,
                "charByteOffset": 18
              },
              "end": {
                "line": 25,
                "charByteOffset": 20
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 25,
          "charByteOffset": 4
        },
        "end": {
          "line": 25,
          "charByteOffset": 21
        }
      }
    }
  ],
  "79": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 25,
          "charByteOffset": 4
        },
        "end": {
          "line": 25,
          "charByteOffset": 21
        }
      }
    }
  ],
  "80": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 26,
          "charByteOffset": 4
        },
        "end": {
          "line": 26,
          "charByteOffset": 21
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 23
    }
  ],
  "81": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "14",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 4
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "14"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 26,
                "charByteOffset": 18
              },
              "end": {
                "line": 26,
                "charByteOffset": 20
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 26,
          "charByteOffset": 4
        },
        "end": {
          "line": 26,
          "charByteOffset": 21
        }
      }
    }
  ],
  "82": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 26,
          "charByteOffset": 4
        },
        "end": {
          "line": 26,
          "charByteOffset": 21
        }
      }
    }
  ],
  "83": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 27,
          "charByteOffset": 4
        },
        "end": {
          "line": 27,
          "charByteOffset": 22
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 24
    }
  ],
  "84": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "ret",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 4
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 27,
                "charByteOffset": 12
              },
              "end": {
                "line": 27,
                "charByteOffset": 15
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 27,
          "charByteOffset": 4
        },
        "end": {
          "line": 27,
          "charByteOffset": 22
        }
      }
    }
  ],
  "85": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "num",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 4
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 27,
                "charByteOffset": 18
              },
              "end": {
                "line": 27,
                "charByteOffset": 21
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 27,
          "charByteOffset": 4
        },
        "end": {
          "line": 27,
          "charByteOffset": 22
        }
      }
    }
  ],
  "86": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "ret",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 4
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 27,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 27,
                  "charByteOffset": 15
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "num",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 4
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 27,
                  "charByteOffset": 18
                },
                "end": {
                  "line": 27,
                  "charByteOffset": 21
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 4
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 27,
                "charByteOffset": 12
              },
              "end": {
                "line": 27,
                "charByteOffset": 21
              }
            }
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "14",
            "tag": {
              "#class": "tac.Tag.Int"
            }
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "ret",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 4
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 27,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 27,
                  "charByteOffset": 15
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "a",
            "tag": {
              "#class": "tac.Tag.Int"
            }
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "num",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 4
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 27,
                  "charByteOffset": 18
                },
                "end": {
                  "line": 27,
                  "charByteOffset": 21
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 27,
          "charByteOffset": 4
        },
        "end": {
          "line": 27,
          "charByteOffset": 22
        }
      }
    }
  ],
  "87": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 27,
          "charByteOffset": 4
        },
        "end": {
          "line": 27,
          "charByteOffset": 22
        }
      }
    }
  ],
  "88": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "ret",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 4
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 28,
                "charByteOffset": 11
              },
              "end": {
                "line": 28,
                "charByteOffset": 14
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 28,
          "charByteOffset": 4
        },
        "end": {
          "line": 28,
          "charByteOffset": 15
        }
      }
    }
  ],
  "89": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 35,
          "charByteOffset": 4
        },
        "end": {
          "line": 35,
          "charByteOffset": 24
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 25
    }
  ],
  "90": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 26
    }
  ],
  "91": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "4",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "4"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 36,
                "charByteOffset": 24
              },
              "end": {
                "line": 36,
                "charByteOffset": 25
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    }
  ],
  "92": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "5",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "5"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 36,
                "charByteOffset": 27
              },
              "end": {
                "line": 36,
                "charByteOffset": 28
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    }
  ],
  "93": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    }
  ],
  "94": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Const",
        "value": "4"
      }
    }
  ],
  "95": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Const",
        "value": "5"
      }
    }
  ],
  "96": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON30",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "97": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON31",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "98": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON32",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "99": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON33",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "100": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON34",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "101": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON35",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "102": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON36",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "103": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON37",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "104": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON38",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "105": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON39",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "106": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON40",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "107": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON41",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "108": [
    {
      "key": {
        "name": "tac.transfers.balance",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    }
  ],
  "109": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacAddress",
        "maybeTACKeywordOrdinal": 22
      }
    },
    {
      "key": {
        "name": "tac.env.known-bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 160
    },
    {
      "key": {
        "name": "tac.contract.sym.addr.name",
        "type": "java.lang.String",
        "erasureStrategy": "Erased"
      },
      "value": "TestContract"
    },
    {
      "key": {
        "name": "tac.contract.sym.addr",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Erased"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "110": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 25,
        "len": 1996,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    }
  ],
  "111": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 75,
        "len": 425,
        "jumpType": "ENTER",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    }
  ],
  "112": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "a",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 3
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 12,
                "charByteOffset": 27
              },
              "end": {
                "line": 12,
                "charByteOffset": 28
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 12,
          "charByteOffset": 4
        },
        "end": {
          "line": 12,
          "charByteOffset": 34
        }
      }
    }
  ],
  "113": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "b",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 3
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 12,
                "charByteOffset": 31
              },
              "end": {
                "line": 12,
                "charByteOffset": 32
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 12,
          "charByteOffset": 4
        },
        "end": {
          "line": 12,
          "charByteOffset": 34
        }
      }
    }
  ],
  "114": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.BinaryExp.AddExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "a",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 3
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 12,
                  "charByteOffset": 27
                },
                "end": {
                  "line": 12,
                  "charByteOffset": 28
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "b",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 3
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 12,
                  "charByteOffset": 31
                },
                "end": {
                  "line": 12,
                  "charByteOffset": 32
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 3
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Mathint"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 12,
                "charByteOffset": 27
              },
              "end": {
                "line": 12,
                "charByteOffset": 32
              }
            }
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "4",
            "tag": {
              "#class": "tac.Tag.Int"
            }
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "a",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 3
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 12,
                  "charByteOffset": 27
                },
                "end": {
                  "line": 12,
                  "charByteOffset": 28
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "5",
            "tag": {
              "#class": "tac.Tag.Int"
            }
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "b",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 3
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 12,
                  "charByteOffset": 31
                },
                "end": {
                  "line": 12,
                  "charByteOffset": 32
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 12,
          "charByteOffset": 4
        },
        "end": {
          "line": 12,
          "charByteOffset": 34
        }
      }
    }
  ],
  "115": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 12,
          "charByteOffset": 4
        },
        "end": {
          "line": 12,
          "charByteOffset": 34
        }
      }
    }
  ],
  "116": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 27
    }
  ],
  "117": [
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Const",
        "value": "9",
        "tag": {
          "#class": "tac.Tag.Int"
        }
      }
    }
  ],
  "118": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 75,
        "len": 425,
        "jumpType": "EXIT",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    }
  ],
  "119": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 36,
          "charByteOffset": 4
        },
        "end": {
          "line": 36,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 75,
        "len": 425,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    }
  ],
  "120": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 28
    }
  ],
  "121": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "7",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "7"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 37,
                "charByteOffset": 27
              },
              "end": {
                "line": 37,
                "charByteOffset": 28
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    }
  ],
  "122": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    }
  ],
  "123": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Const",
        "value": "7"
      }
    }
  ],
  "124": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON62",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "125": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON63",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "126": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON64",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "127": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON65",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "128": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON66",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "129": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON67",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "130": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON68",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "131": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON69",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "132": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON70",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "133": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON71",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "134": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON72",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "135": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON73",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0,
        "meta": [
          {
            "key": {
              "name": "tac.is-temp-var",
              "type": "tac.MetaMap$Companion$NothingValue",
              "erasureStrategy": "Canonical"
            },
            "value": {
            }
          }
        ]
      }
    }
  ],
  "136": [
    {
      "key": {
        "name": "tac.transfers.balance",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    }
  ],
  "137": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 25,
        "len": 1996,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    }
  ],
  "138": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 506,
        "len": 417,
        "jumpType": "ENTER",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    }
  ],
  "139": [
    {
      "key": {
        "name": "assert.format.arg.1",
        "type": "vc.data.TACSymbol",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.Full",
        "namePrefix": "CANON83",
        "tag": {
          "#class": "tac.Tag.Int"
        },
        "callIndex": 0
      }
    }
  ],
  "140": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 506,
        "len": 417,
        "jumpType": "EXIT",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    }
  ],
  "141": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 37,
          "charByteOffset": 4
        },
        "end": {
          "line": 37,
          "charByteOffset": 30
        }
      }
    },
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 506,
        "len": 417,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    }
  ],
  "142": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 38,
          "charByteOffset": 4
        },
        "end": {
          "line": 38,
          "charByteOffset": 26
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 29
    }
  ],
  "143": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 38,
          "charByteOffset": 4
        },
        "end": {
          "line": 38,
          "charByteOffset": 26
        }
      }
    }
  ],
  "144": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 38,
          "charByteOffset": 4
        },
        "end": {
          "line": 38,
          "charByteOffset": 26
        }
      }
    },
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 25,
        "len": 1996,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    }
  ],
  "145": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 38,
          "charByteOffset": 4
        },
        "end": {
          "line": 38,
          "charByteOffset": 26
        }
      }
    },
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 929,
        "len": 328,
        "jumpType": "ENTER",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    }
  ],
  "146": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 30
    }
  ],
  "147": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "1",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.HookScopeItem",
                  "scopeId": 5
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "1"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 16,
                "charByteOffset": 26
              },
              "end": {
                "line": 16,
                "charByteOffset": 27
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 16,
          "charByteOffset": 4
        },
        "end": {
          "line": 16,
          "charByteOffset": 28
        }
      }
    }
  ],
  "148": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "contractVal",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.HookScopeItem",
                    "scopeId": 5
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.VM",
                "descriptor": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                  "bitwidth": 256
                },
                "context": {
                  "#class": "spec.cvlast.typedescriptors.FromVMContext.HookValue"
                }
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 16,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 16,
                  "charByteOffset": 23
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "1",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.HookScopeItem",
                    "scopeId": 5
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "1"
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 16,
                  "charByteOffset": 26
                },
                "end": {
                  "line": 16,
                  "charByteOffset": 27
                }
              }
            }
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.HookScopeItem",
                  "scopeId": 5
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 16,
                "charByteOffset": 12
              },
              "end": {
                "line": 16,
                "charByteOffset": 27
              }
            }
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Var.Full",
            "namePrefix": "CANON88!!8",
            "tag": {
              "#class": "tac.Tag.Bit256"
            },
            "callIndex": 0,
            "meta": [
              {
                "key": {
                  "name": "tac.storage.non-indexed-path.family",
                  "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
                  "erasureStrategy": "Canonical"
                },
                "value": {
                  "storagePaths": [
                    {
                      "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                      "slot": "0"
                    }
                  ]
                }
              },
              {
                "key": {
                  "name": "Tac.symbol.keyword",
                  "type": "vc.data.TACSymbol$Var$KeywordEntry",
                  "erasureStrategy": "Canonical"
                },
                "value": {
                  "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                  "name": "L",
                  "maybeTACKeywordOrdinal": 45
                }
              },
              {
                "key": {
                  "name": "tac.scalarization.sort",
                  "type": "vc.data.ScalarizationSort",
                  "erasureStrategy": "Canonical"
                },
                "value": {
                  "#class": "vc.data.ScalarizationSort.Split",
                  "idx": "0"
                }
              },
              {
                "key": {
                  "name": "tac.storage.bit-width",
                  "type": "java.lang.Integer",
                  "erasureStrategy": "Canonical"
                },
                "value": 256
              },
              {
                "key": {
                  "name": "tac.storage.pretty.paths",
                  "type": "analysis.storage.DisplayPaths",
                  "erasureStrategy": "Erased"
                },
                "value": {
                  "paths": [
                    {
                      "#class": "analysis.storage.DisplayPath.Root",
                      "name": "val"
                    }
                  ]
                }
              },
              {
                "key": {
                  "name": "tac.slot.type",
                  "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
                  "erasureStrategy": "Canonical"
                },
                "value": {
                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                  "bitwidth": 256
                }
              },
              {
                "key": {
                  "name": "tac.storage.non-indexed-path",
                  "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
                  "erasureStrategy": "Canonical"
                },
                "value": {
                  "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                  "slot": "0"
                }
              },
              {
                "key": {
                  "name": "tac.storage",
                  "type": "java.math.BigInteger",
                  "erasureStrategy": "Canonical"
                },
                "value": "ce4604a0000000000000000000000001"
              },
              {
                "key": {
                  "name": "tac.stack.height",
                  "type": "java.lang.Integer",
                  "erasureStrategy": "Canonical"
                },
                "value": 1021
              }
            ]
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "contractVal",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.HookScopeItem",
                    "scopeId": 5
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.VM",
                "descriptor": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                  "bitwidth": 256
                },
                "context": {
                  "#class": "spec.cvlast.typedescriptors.FromVMContext.HookValue"
                }
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 16,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 16,
                  "charByteOffset": 23
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Var.Full",
            "namePrefix": "CANON91",
            "tag": {
              "#class": "tac.Tag.Int"
            },
            "callIndex": 0
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "1",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.HookScopeItem",
                    "scopeId": 5
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "1"
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 16,
                  "charByteOffset": 26
                },
                "end": {
                  "line": 16,
                  "charByteOffset": 27
                }
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 16,
          "charByteOffset": 4
        },
        "end": {
          "line": 16,
          "charByteOffset": 28
        }
      }
    }
  ],
  "149": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "innerVal",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.HookScopeItem",
                  "scopeId": 5
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 17,
                "charByteOffset": 12
              },
              "end": {
                "line": 17,
                "charByteOffset": 20
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 17,
          "charByteOffset": 4
        },
        "end": {
          "line": 17,
          "charByteOffset": 36
        }
      }
    }
  ],
  "150": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 17,
          "charByteOffset": 4
        },
        "end": {
          "line": 17,
          "charByteOffset": 36
        }
      }
    }
  ],
  "151": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.RelopExp.EqExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "innerVal",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.HookScopeItem",
                    "scopeId": 5
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 17,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 17,
                  "charByteOffset": 20
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "contractVal",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.HookScopeItem",
                    "scopeId": 5
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.VM",
                "descriptor": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                  "bitwidth": 256
                },
                "context": {
                  "#class": "spec.cvlast.typedescriptors.FromVMContext.HookValue"
                }
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 17,
                  "charByteOffset": 24
                },
                "end": {
                  "line": 17,
                  "charByteOffset": 35
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.HookScopeItem",
                  "scopeId": 5
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 17,
                "charByteOffset": 12
              },
              "end": {
                "line": 17,
                "charByteOffset": 35
              }
            }
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Var.Full",
            "namePrefix": "I81",
            "tag": {
              "#class": "tac.Tag.Int"
            },
            "callIndex": 0
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "innerVal",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.HookScopeItem",
                    "scopeId": 5
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 17,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 17,
                  "charByteOffset": 20
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Var.Full",
            "namePrefix": "CANON88!!8",
            "tag": {
              "#class": "tac.Tag.Bit256"
            },
            "callIndex": 0,
            "meta": [
              {
                "key": {
                  "name": "tac.storage.non-indexed-path.family",
                  "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
                  "erasureStrategy": "Canonical"
                },
                "value": {
                  "storagePaths": [
                    {
                      "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                      "slot": "0"
                    }
                  ]
                }
              },
              {
                "key": {
                  "name": "Tac.symbol.keyword",
                  "type": "vc.data.TACSymbol$Var$KeywordEntry",
                  "erasureStrategy": "Canonical"
                },
                "value": {
                  "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                  "name": "L",
                  "maybeTACKeywordOrdinal": 45
                }
              },
              {
                "key": {
                  "name": "tac.scalarization.sort",
                  "type": "vc.data.ScalarizationSort",
                  "erasureStrategy": "Canonical"
                },
                "value": {
                  "#class": "vc.data.ScalarizationSort.Split",
                  "idx": "0"
                }
              },
              {
                "key": {
                  "name": "tac.storage.bit-width",
                  "type": "java.lang.Integer",
                  "erasureStrategy": "Canonical"
                },
                "value": 256
              },
              {
                "key": {
                  "name": "tac.storage.pretty.paths",
                  "type": "analysis.storage.DisplayPaths",
                  "erasureStrategy": "Erased"
                },
                "value": {
                  "paths": [
                    {
                      "#class": "analysis.storage.DisplayPath.Root",
                      "name": "val"
                    }
                  ]
                }
              },
              {
                "key": {
                  "name": "tac.slot.type",
                  "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
                  "erasureStrategy": "Canonical"
                },
                "value": {
                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                  "bitwidth": 256
                }
              },
              {
                "key": {
                  "name": "tac.storage.non-indexed-path",
                  "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
                  "erasureStrategy": "Canonical"
                },
                "value": {
                  "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                  "slot": "0"
                }
              },
              {
                "key": {
                  "name": "tac.storage",
                  "type": "java.math.BigInteger",
                  "erasureStrategy": "Canonical"
                },
                "value": "ce4604a0000000000000000000000001"
              },
              {
                "key": {
                  "name": "tac.stack.height",
                  "type": "java.lang.Integer",
                  "erasureStrategy": "Canonical"
                },
                "value": 1021
              }
            ]
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "contractVal",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.HookScopeItem",
                    "scopeId": 5
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.VM",
                "descriptor": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                  "bitwidth": 256
                },
                "context": {
                  "#class": "spec.cvlast.typedescriptors.FromVMContext.HookValue"
                }
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 17,
                  "charByteOffset": 24
                },
                "end": {
                  "line": 17,
                  "charByteOffset": 35
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 17,
          "charByteOffset": 4
        },
        "end": {
          "line": 17,
          "charByteOffset": 36
        }
      }
    }
  ],
  "152": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 38,
          "charByteOffset": 4
        },
        "end": {
          "line": 38,
          "charByteOffset": 26
        }
      }
    },
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 929,
        "len": 328,
        "jumpType": "EXIT",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    }
  ],
  "153": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 38,
          "charByteOffset": 4
        },
        "end": {
          "line": 38,
          "charByteOffset": 26
        }
      }
    },
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 929,
        "len": 328,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    }
  ],
  "154": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 39,
          "charByteOffset": 4
        },
        "end": {
          "line": 39,
          "charByteOffset": 20
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 31
    }
  ],
  "155": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "t",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 39,
                "charByteOffset": 12
              },
              "end": {
                "line": 39,
                "charByteOffset": 13
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 39,
          "charByteOffset": 4
        },
        "end": {
          "line": 39,
          "charByteOffset": 20
        }
      }
    }
  ],
  "156": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "num",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 39,
                "charByteOffset": 16
              },
              "end": {
                "line": 39,
                "charByteOffset": 19
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 39,
          "charByteOffset": 4
        },
        "end": {
          "line": 39,
          "charByteOffset": 20
        }
      }
    }
  ],
  "157": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "t",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 39,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 39,
                  "charByteOffset": 13
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "num",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 39,
                  "charByteOffset": 16
                },
                "end": {
                  "line": 39,
                  "charByteOffset": 19
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 39,
                "charByteOffset": 12
              },
              "end": {
                "line": 39,
                "charByteOffset": 19
              }
            }
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Var.Full",
            "namePrefix": "I86",
            "tag": {
              "#class": "tac.Tag.Int"
            },
            "callIndex": 0
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "t",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 39,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 39,
                  "charByteOffset": 13
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "5",
            "tag": {
              "#class": "tac.Tag.Int"
            }
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "num",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 39,
                  "charByteOffset": 16
                },
                "end": {
                  "line": 39,
                  "charByteOffset": 19
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 39,
          "charByteOffset": 4
        },
        "end": {
          "line": 39,
          "charByteOffset": 20
        }
      }
    }
  ],
  "158": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 39,
          "charByteOffset": 4
        },
        "end": {
          "line": 39,
          "charByteOffset": 20
        }
      }
    }
  ],
  "159": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 40,
          "charByteOffset": 4
        },
        "end": {
          "line": 40,
          "charByteOffset": 20
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 32
    }
  ],
  "160": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "t",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 40,
                "charByteOffset": 12
              },
              "end": {
                "line": 40,
                "charByteOffset": 13
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 40,
          "charByteOffset": 4
        },
        "end": {
          "line": 40,
          "charByteOffset": 20
        }
      }
    }
  ],
  "161": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "r1",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 40,
                "charByteOffset": 17
              },
              "end": {
                "line": 40,
                "charByteOffset": 19
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 40,
          "charByteOffset": 4
        },
        "end": {
          "line": 40,
          "charByteOffset": 20
        }
      }
    }
  ],
  "162": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.RelopExp.EqExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "t",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 40,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 40,
                  "charByteOffset": 13
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "r1",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 40,
                  "charByteOffset": 17
                },
                "end": {
                  "line": 40,
                  "charByteOffset": 19
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 40,
                "charByteOffset": 12
              },
              "end": {
                "line": 40,
                "charByteOffset": 19
              }
            }
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Var.Full",
            "namePrefix": "I89",
            "tag": {
              "#class": "tac.Tag.Int"
            },
            "callIndex": 0
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "t",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 40,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 40,
                  "charByteOffset": 13
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "14",
            "tag": {
              "#class": "tac.Tag.Int"
            }
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "r1",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 40,
                  "charByteOffset": 17
                },
                "end": {
                  "line": 40,
                  "charByteOffset": 19
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 40,
          "charByteOffset": 4
        },
        "end": {
          "line": 40,
          "charByteOffset": 20
        }
      }
    }
  ],
  "163": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 40,
          "charByteOffset": 4
        },
        "end": {
          "line": 40,
          "charByteOffset": 20
        }
      }
    }
  ],
  "164": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 41,
          "charByteOffset": 4
        },
        "end": {
          "line": 41,
          "charByteOffset": 19
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 33
    }
  ],
  "165": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "r2",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 41,
                "charByteOffset": 11
              },
              "end": {
                "line": 41,
                "charByteOffset": 13
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 41,
          "charByteOffset": 4
        },
        "end": {
          "line": 41,
          "charByteOffset": 19
        }
      }
    }
  ],
  "166": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "9",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "9"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 41,
                "charByteOffset": 17
              },
              "end": {
                "line": 41,
                "charByteOffset": 18
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 41,
          "charByteOffset": 4
        },
        "end": {
          "line": 41,
          "charByteOffset": 19
        }
      }
    }
  ],
  "167": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.RelopExp.EqExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "r2",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 41,
                  "charByteOffset": 11
                },
                "end": {
                  "line": 41,
                  "charByteOffset": 13
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "9",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "9"
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 41,
                  "charByteOffset": 17
                },
                "end": {
                  "line": 41,
                  "charByteOffset": 18
                }
              }
            }
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 41,
                "charByteOffset": 11
              },
              "end": {
                "line": 41,
                "charByteOffset": 18
              }
            }
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Var.Full",
            "namePrefix": "I91",
            "tag": {
              "#class": "tac.Tag.Int"
            },
            "callIndex": 0
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "r2",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 41,
                  "charByteOffset": 11
                },
                "end": {
                  "line": 41,
                  "charByteOffset": 13
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "9"
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "9",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "9"
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 41,
                  "charByteOffset": 17
                },
                "end": {
                  "line": 41,
                  "charByteOffset": 18
                }
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 41,
          "charByteOffset": 4
        },
        "end": {
          "line": 41,
          "charByteOffset": 19
        }
      }
    }
  ],
  "168": [
    {
      "key": {
        "name": "cvl.user.defined.assert",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 41,
          "charByteOffset": 4
        },
        "end": {
          "line": 41,
          "charByteOffset": 19
        }
      }
    }
  ],
  "169": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 41,
          "charByteOffset": 4
        },
        "end": {
          "line": 41,
          "charByteOffset": 19
        }
      }
    }
  ],
  "170": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 42,
          "charByteOffset": 4
        },
        "end": {
          "line": 42,
          "charByteOffset": 20
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 34
    }
  ],
  "171": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "r3",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 42,
                "charByteOffset": 11
              },
              "end": {
                "line": 42,
                "charByteOffset": 13
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 42,
          "charByteOffset": 4
        },
        "end": {
          "line": 42,
          "charByteOffset": 20
        }
      }
    }
  ],
  "172": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "e",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "e"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 42,
                "charByteOffset": 17
              },
              "end": {
                "line": 42,
                "charByteOffset": 19
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 42,
          "charByteOffset": 4
        },
        "end": {
          "line": 42,
          "charByteOffset": 20
        }
      }
    }
  ],
  "173": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.RelopExp.EqExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "r3",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 42,
                  "charByteOffset": 11
                },
                "end": {
                  "line": 42,
                  "charByteOffset": 13
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "e",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "e"
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 42,
                  "charByteOffset": 17
                },
                "end": {
                  "line": 42,
                  "charByteOffset": 19
                }
              }
            }
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 42,
                "charByteOffset": 11
              },
              "end": {
                "line": 42,
                "charByteOffset": 19
              }
            }
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Var.Full",
            "namePrefix": "I93",
            "tag": {
              "#class": "tac.Tag.Int"
            },
            "callIndex": 0
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "r3",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 42,
                  "charByteOffset": 11
                },
                "end": {
                  "line": 42,
                  "charByteOffset": 13
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "e"
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "e",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "e"
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 42,
                  "charByteOffset": 17
                },
                "end": {
                  "line": 42,
                  "charByteOffset": 19
                }
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 42,
          "charByteOffset": 4
        },
        "end": {
          "line": 42,
          "charByteOffset": 20
        }
      }
    }
  ],
  "174": [
    {
      "key": {
        "name": "cvl.user.defined.assert",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 42,
          "charByteOffset": 4
        },
        "end": {
          "line": 42,
          "charByteOffset": 20
        }
      }
    }
  ],
  "175": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 42,
          "charByteOffset": 4
        },
        "end": {
          "line": 42,
          "charByteOffset": 20
        }
      }
    }
  ],
  "176": [
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 43,
          "charByteOffset": 4
        },
        "end": {
          "line": 43,
          "charByteOffset": 19
        }
      }
    },
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 35
    }
  ],
  "177": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "r4",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 43,
                "charByteOffset": 11
              },
              "end": {
                "line": 43,
                "charByteOffset": 13
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 43,
          "charByteOffset": 4
        },
        "end": {
          "line": 43,
          "charByteOffset": 19
        }
      }
    }
  ],
  "178": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "1",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "1"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 43,
                "charByteOffset": 17
              },
              "end": {
                "line": 43,
                "charByteOffset": 18
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 43,
          "charByteOffset": 4
        },
        "end": {
          "line": 43,
          "charByteOffset": 19
        }
      }
    }
  ],
  "179": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.RelopExp.EqExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "r4",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 43,
                  "charByteOffset": 11
                },
                "end": {
                  "line": 43,
                  "charByteOffset": 13
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "1",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "1"
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 43,
                  "charByteOffset": 17
                },
                "end": {
                  "line": 43,
                  "charByteOffset": 18
                }
              }
            }
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 2
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "cvlRange": {
              "#class": "spec.cvlast.CVLRange.Range",
              "specFile": "Basic.spec",
              "start": {
                "line": 43,
                "charByteOffset": 11
              },
              "end": {
                "line": 43,
                "charByteOffset": 18
              }
            }
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Var.Full",
            "namePrefix": "I96",
            "tag": {
              "#class": "tac.Tag.Int"
            },
            "callIndex": 0
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "r4",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 43,
                  "charByteOffset": 11
                },
                "end": {
                  "line": 43,
                  "charByteOffset": 13
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Var.Full",
            "namePrefix": "CANON110",
            "tag": {
              "#class": "tac.Tag.Int"
            },
            "callIndex": 0
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "1",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 2
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "1"
              },
              "cvlRange": {
                "#class": "spec.cvlast.CVLRange.Range",
                "specFile": "Basic.spec",
                "start": {
                  "line": 43,
                  "charByteOffset": 17
                },
                "end": {
                  "line": 43,
                  "charByteOffset": 18
                }
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 43,
          "charByteOffset": 4
        },
        "end": {
          "line": 43,
          "charByteOffset": 19
        }
      }
    }
  ],
  "180": [
    {
      "key": {
        "name": "cvl.user.defined.assert",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "spec.cvlast.CVLRange",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLRange.Range",
        "specFile": "Basic.spec",
        "start": {
          "line": 43,
          "charByteOffset": 4
        },
        "end": {
          "line": 43,
          "charByteOffset": 19
        }
      }
    }
  ]
}