pragma solidity ^0.8.10;

contract MultipleCandidates {
    int n;

    function plus_one() public {
        n += 1;
    }

    function minus_one() public {
        n -= 1;
    }
}
