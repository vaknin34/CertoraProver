methods {
    function _._ external => DISPATCH [
        C.bar(uint),
        _.update(uint),
        Other._
    ] default NONDET ;
}

rule easy {
    assert true;
}
