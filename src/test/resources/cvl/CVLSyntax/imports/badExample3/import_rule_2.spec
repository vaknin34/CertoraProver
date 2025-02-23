import "b.spec";

rule inv_instate_sanity() { // Should *not* collide with the rule sanity auto-generated rule

    assert false;
}

function fooInC(uint256 i) { require i > 9; }


rule inv_instate(address addr) { // Should collide with an auto-generated invariant rule
    assert false;
}

invariant inv() getSomeUInt() >= 7 {
	preserved minusSevenSomeUInt() with (env e) {
		env e1;
        plusSevenSomeUInt(e1);
	}
}

use rule hasDelegateCalls;

use builtin rule hasDelegateCalls;
