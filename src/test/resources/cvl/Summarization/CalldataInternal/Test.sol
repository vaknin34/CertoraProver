contract Test {
	struct NextField {
		uint nested1;
		uint[] nested2;
	}

	struct StaticStruct {
		uint x;
		uint y;
	}
	
	struct Complex {
		uint a;
		uint[] b;
		uint[3] c;
		bytes d;
		NextField f;
	}

	struct TooComplex {
		Complex[] list;
	}

	uint counter;

	modifier getWrekt {
		counter++;
		_;
	}
	
	function myInternal1(bytes calldata z) internal returns (uint) {
		return z.length;
	}

	function myInternal2(NextField calldata f) internal getWrekt returns (uint) {
		return f.nested2.length;
	}

	function myInternal3(uint a, Complex calldata) internal returns (uint) {
		return a;
	}

	function myInternal4(TooComplex calldata z) internal returns (uint) {
		return z.list.length;
	}

	function myInternal5(uint[] calldata g) internal returns (uint) {
		return g.length;
	}

	function myInternal6(uint[3] calldata a) internal returns (uint) {
		return 5;
	}

	function myInternal7(StaticStruct[] calldata a) internal returns (uint) {
		return a.length;
	}

	function entryPoint1(TooComplex calldata tc) external returns (uint, uint, uint, uint, uint, uint) {
		return (
				myInternal1(tc.list[2].d),
				myInternal2(tc.list[1].f),
				myInternal3(counter, tc.list[1]),
				myInternal4(tc),
				myInternal5(tc.list[0].b),
				myInternal6(tc.list[1].c)
		);
	}

	function entryPoint2(StaticStruct[] calldata z) external returns (uint) {
		return myInternal7(z);
	}
}
