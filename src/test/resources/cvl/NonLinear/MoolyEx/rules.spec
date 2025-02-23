methods {
	function f1(uint256,uint256) external returns uint256 envfree;
	function f2(uint256,uint256) external returns uint256 envfree;
	function f1b(uint256,uint256) external returns uint256 envfree;
	function f2b(uint256,uint256) external returns uint256 envfree;

}
rule r1(uint x, uint y) {
	assert f1(x,y) >= f2(x,y);
}

rule r2(uint x, uint y) {
	require y >= x;
	assert f1(x,y) == f2(x,y);
}

rule r1b(uint x, uint y) {
	assert f1b(x,y) >= f2b(x,y);
}

rule r2b(uint x, uint y) {
	require y >= x;
	assert f1b(x,y) == f2b(x,y);
}
