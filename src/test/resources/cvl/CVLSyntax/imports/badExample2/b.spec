import "c.spec";

definition ruleInB() returns uint = 0;

rule ruleInB {
    assert false;
}

ghost ghostInB() returns uint;

rule hasDelegateCalls(bool b) {
    assert b, "to b or not to b";
}
