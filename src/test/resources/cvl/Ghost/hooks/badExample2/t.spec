sort foo;

ghost ghostX(foo) returns uint256;

ghost blaze(uint) returns uint {
    axiom forall uint256 x. blaze(x) == x;
}

hook Sstore (slot 0) uint i {
    uint256 my_collided_variable2 = i;
    if (my_collided_variable2 == 1) {
        assert false;
    } else {
        assert true;
    }
    havoc ghostX assuming forall foo x. ghostX@new(x) == blaze(my_collided_variable2);
}
