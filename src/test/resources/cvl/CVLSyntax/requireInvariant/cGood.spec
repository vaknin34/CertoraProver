ghost g(uint) returns uint
{
	init_state axiom forall uint x. g(x) >= 10;
}

invariant gInv(uint x) g(x) >= 10;

rule r(uint x) {
	requireInvariant gInv(x);
	assert g(x) >= 8;
}
