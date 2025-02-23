using C as c;
using D as d;

function acceptsIntArray(int32[] arr) {
    assert arr.length == 4;
    assert arr[0] == -1;
    assert arr[1] == 2^31-1;
}

function acceptsAddressArray(address[] arr) {
    assert arr.length == 5;
    assert arr[0] == 0;
    assert arr[1] == max_address;
    assert arr[2] == c;
    assert arr[3] == d;
}

function acceptsNestedArray(int8[][] arr) {}

rule callIntArray {
    int16 i;
    uint24 u;
    int32[] arr = [-1, 2^31-1, i, u];
    acceptsIntArray(arr);
    acceptsIntArray([-1, 2^31-1, i, u]); // no type hint in this case
}

rule callAddressArray {
    address a;
    address[] arr = [0, max_address, c, d, a];
    acceptsAddressArray(arr);
    acceptsAddressArray([0, max_address, c, d, a]); // no type hint in this case
}

rule callNestedArray {
    int8 i; int8 j;
    int8 [] inner = [i, j];
    int8[][] arr = [[1,2,3], [2^7-1, -2^7], inner];
    acceptsNestedArray(arr);
    assert true;
}
