methods {
	function myInternal1(bytes calldata z) internal returns (uint) => the_ghost(z);
	function myInternal2(Test.NextField calldata f) internal returns (uint) => internal2Summary(f);
	function myInternal3(uint a, Test.Complex calldata b) internal returns (uint) => internal3Summary(b);

	function myInternal5(uint[] calldata a) internal returns (uint) => internal5Summary(a);
	function myInternal6(uint[3] calldata b) internal returns (uint) => internal6Summary(b);
	function myInternal7(Test.StaticStruct[] calldata a) internal returns (uint) => internal7Summary(a);
}

ghost the_ghost(bytes) returns uint;

function internal2Summary(Test.NextField next) returns uint {
	return next.nested1;
}

function internal3Summary(Test.Complex complex) returns uint {
	return complex.a;
}

function internal5Summary(uint[] b) returns uint {
	require(b.length > 0);
	return b[0];
}

function internal6Summary(uint[3] c) returns uint {
	return c[0];
}

function internal7Summary(Test.StaticStruct[] a) returns uint {
	require(a.length > 1);
	return a[1].y;
}

rule test {
	env e;
	Test.TooComplex arg1;
	uint r1;
	uint r2;
	uint r3;
	uint r5;
	uint r6;

	r1, r2, r3, _, r5, r6 = entryPoint1(e, arg1);

	assert r1 == the_ghost(arg1.list[2].d), "internal1";
	assert r2 == arg1.list[1].f.nested1, "internal2";
	assert r3 == arg1.list[1].a, "internal3";
	assert r5 == arg1.list[0].b[0], "internal5";
	assert r6 == arg1.list[1].c[0], "internal6";

	Test.StaticStruct[] arg2;
	uint r7 = entryPoint2(e, arg2);
	assert r7 == arg2[1].y;
}
