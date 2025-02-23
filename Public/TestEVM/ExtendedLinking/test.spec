using DelegateMixin1 as mixin1;
using DelegateMixin2 as mixin2;
using DelegateStorage as delegate;
using WithCollision as collide;

methods {
    function WithCollision.getCallee() internal returns (address) => delegate;
    function Test.getCalleeVirt(bool selector) internal returns (address) => calleeVirt(selector);
    function Test.getCallee() internal returns (address) => delegate;
}

function calleeVirt(bool selector) returns address {
    if(selector) {
        return mixin1;
    } else {
        return mixin2;
    }
}

rule basic_delegation_and_rollback(env e) {
    uint f;
    storage backup = lastStorage;
    uint prev = doGet(e);
    doSet(e, f);
    assert doGet(e) == f;
    uint d = doGet(e) at backup;
    assert d == prev;
}

rule mixed_delegation_and_rollback(env e) {
    uint mixinField1;
    uint mixinField2;
    storage backup = lastStorage;
    uint field1Backup = doGet(e, true);
    uint field2Backup = doGet(e, false);

    doSet(e,mixinField1, true);
    doSet(e,mixinField2, false);

    assert doGet(e, true) == mixinField1;
    assert doGet(e, false) == mixinField2;

    uint rollback1 = doGet(e, true) at backup;
    assert rollback1 == field1Backup;
    assert doGet(e, false) == field2Backup;
}

rule collide_should_fail(env e) {
    uint f;
    collide.doSet(e, f);
    assert collide.doGet(e) == f;
}