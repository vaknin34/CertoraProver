# Certora Equivalence Checker
## Description
The Equivalence Checker (`certoraEqCheck`) can be used to compare any two pure functions using the Certora Prover tool.
It also works for checking the equivalence of two view functions from the same contract.
It generates a specification written in CVL, the language of the Certora Prover,
along with a `.conf` file for to running the tool.

## Usage
`certoraEqCheck` can be run either in default (`def`) mode, in which you supply all the required information as command line arguments (see below), or in `conf` mode where you supply a `conf` file along with optional arguments.

### Default mode:
```
certoraEqCheck def "path_to_file:contract:function:solc" "path_to_file:contract:function:solc"
```
Example:
```
certoraEqCheck def Test/EqCheck/BasicMathGood.sol:add:solc8.0 Test/EqCheck/BasicMathBad.sol:add_pass:solc8.0
```

In the above example,
`solc` is the name of the executable for the Solidity compiler version you are using.
The Solidity compilers do not need to be the same for both arguments to `CertoraEqCheck`,
it just need to be appropriate for the given contract.


### Configuration mode:
```
certoraEqCheck conf <path_to_conf>.conf contract:function contract:function
```
Example:
```
certoraEqCheck conf Test/EqCheck/testGood.conf BasicMathGood:add BasicMathBad:add_mult
```

Use `--bitvector` if you are comparing any functions with bitwise operations.
This will slow down the tool slightly, but ensure that the results are sound in this case.

Note that the contracts can be omitted if the contract name is the same as that of the file.
