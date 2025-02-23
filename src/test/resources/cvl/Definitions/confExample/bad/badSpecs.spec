sort foo;
sort bar;

// error when parameters used incorrectly inside body
// (param types properly bound in type environment)
definition d1(foo x, bar y) returns bool = x == y;

ghost g1(foo) returns bool;
ghost g2(foo) returns bool;

// error if param type is undefined
definition undefinedParam(baz x) returns bar = x + 5;
// error if return type is undefined
definition d2(uint x) returns baz = x + 6;
// error if declared return type does not match function body
definition d3(uint x, uint y) returns uint = x < y;

// error if multiple parameters have the same name
definition d4(uint x, uint x) returns uint = x + x;

definition dg1new(foo x) returns bool = g1@new(x);
definition dg1old(foo x) returns bool = g1@old(x);
definition dg1(foo x) returns bool = g1(x);
definition dg1oldg2(foo x) returns bool = g1@old(x) && g2(x);

definition dg1g2(foo x) returns bool = g1(x) && g2(x);
// error, this both reads and "modifies" g1
definition readAndModify(foo x) returns bool = dg1g2(x) && dg1new(x);

rule r1 {
    foo f1;
    // error to use variable in one-state sense in two-state context
    havoc g1 assuming dg1(f1);
    havoc g1, g2 assuming dg1oldg2(f1);

    // error to use variable in two-state sense in one-state context
    require dg1new(f1);
    require dg1old(f1);

    // error to shadow 
    havoc g1 assuming forall foo g1. dg1new(g1);

    assert true;
}
