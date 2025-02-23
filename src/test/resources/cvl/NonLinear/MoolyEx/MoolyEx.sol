contract MoolyEx {

	function max(uint z, uint t) public returns (uint) {
		if (z>t) return z;
		else return t;
	}

	function safeMul(uint x, uint y) public returns (uint) {
		uint c = x*y;
		if (x == 0) {
			return 0;
		}
		require(c/x == y);
		return c;
	}
	
	function f1(uint x, uint y) public returns (uint) {
		return max(x,y) * x;
	}
	
	function f2(uint x, uint y) public returns (uint) {
		return y*x;
	}
	
	
	function f1b(uint x, uint y) public returns (uint) {
		return safeMul(max(x,y), x);
	}
	
	function f2b(uint x, uint y) public returns (uint) {
		return safeMul(y,x);
	}
}