methods {
  function getSomeUInt() external returns(uint256) envfree;
}

function fooInC(uint256 i) { require i > 9; }

rule badRuleInC(method f) {
	assert getSomeUInt();
}

rule ruleInC(uint u) { 
	assert u > 8;
}

rule parametricRuleInC(method f, method g) filtered { g -> g.selector == sig:getSomeUInt().selector } {
	env e;
	calldataarg args;
	f(e, args);
	g(e, args);
	
	assert false;
}
