import "d.spec";

invariant inv(address a) a == 0;

invariant inv() getSomeUInt() >= 7 {
	preserved minusSevenSomeUInt() with (env e) {
		env e1;
        plusSevenSomeUInt(e1);
	}
}

use rule hasDelegateCalls;

use builtin rule hasDelegateCalls;
