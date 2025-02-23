sort foo;
sort bar;

ghost g0(foo) returns bar;

ghost g1(foo) returns bar;

ghost g2(foo, bar) returns bar {
    // error when axiom refers to ghost other than itself (g1 here)
    axiom forall foo x. forall bar y. g1(x) == g2(x, y);
}

rule r1 {
    foo f1;
    bar b1;
    bar b2;
    // error when referring to 1 state version of ghost or variable in a two state context
    havoc g1 assuming g1(f1) == b1;
    // error when referring to 2 state version of ghost or variable in a one state context
    b2 = g1@new(f1@old);
    assert true;
}
