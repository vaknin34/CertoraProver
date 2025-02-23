/*
 *     The Certora Prover
 *     Copyright (C) 2025  Certora Ltd.
 *
 *     This program is free software: you can redistribute it and/or modify
 *     it under the terms of the GNU General Public License as published by
 *     the Free Software Foundation, version 3 of the License.
 *
 *     This program is distributed in the hope that it will be useful,
 *     but WITHOUT ANY WARRANTY; without even the implied warranty of
 *     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *     GNU General Public License for more details.
 *
 *     You should have received a copy of the GNU General Public License
 *     along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package pipeline

import loaders.SolidityContractTest
import loaders.WithResourceFile
import normalizer.DummyJumpNodeNormalizer
import org.junit.jupiter.api.Assertions
import verifier.ContractUtils.computeMethodsInCode

abstract class DecomposeTest : SolidityContractTest, WithResourceFile {
    fun testHarness(solc: String, contractSource: String, expectedNumOfMethods: Int) {
        val contractObjectCode = loadDecompiled(contractSource, solc)
        // compute methods: big part of the test is about making sure this succeeds
        val mapOfMethods = computeMethodsInCode(contractObjectCode)

        Assertions.assertEquals(expectedNumOfMethods, mapOfMethods.size)
        mapOfMethods.values.forEach { m ->
            Assertions.assertEquals(1, m.analysisCache.graph.roots.size)
        }
    }

    abstract val FALLBACK: String
    abstract fun IMMUTABLE(solc: String): String

    // all contracts to test matches to the number of expected functions
    fun contractNoLoops() = """contract Test {
                  function test(uint x, uint y) public returns (uint) {
                    return add(x,y);
                  }

                  function add(uint x, uint y) public returns (uint) { return x+y; }
                }
            """ to 3

    fun contractWithLoops1() = """contract Test {
                  function test(uint x, uint[] memory y) public returns (uint) {
                    return add(x,y[0]);
                  }

                  function add(uint x, uint y) public returns (uint) { return x+y; }
                }
            """ to 3

    fun contractWithLoops2() = """contract Test {
                  function test(uint x, uint[] memory y) public returns (uint) {
                    uint sum = x;
                    for (uint i = 0 ; i < y.length ; i++) {
                        sum = add(sum, y[0]);
                    }
                    return sum;
                  }

                  function add(uint x, uint y) public returns (uint) { return x+y; }
                }
            """ to 3

    fun contractWithExplicityPayableFallback() = """
                contract Test {
                    uint x;
                    uint y;
                    ${FALLBACK} payable external {
                        msg.sender.send(x+y-msg.value);
                    }
                }
            """.trimIndent() to 1

    fun contractWithExplicityPayableFallbackAndANonPayableFunction() = """
                contract Test {
                    uint x;
                    uint y;
                    ${FALLBACK} payable external {
                        msg.sender.send(x+y-msg.value);
                    }

                    function f() public returns (uint) { return x + y; }
                }
            """.trimIndent() to 2

    fun contractWithExplicitPayableFallbackAndAPayableFunction() = """
                contract Test {
                    uint x;
                    uint y;
                    ${FALLBACK} payable external {
                        msg.sender.send(x+y-msg.value);
                    }

                    function f() public payable returns (uint) { return x + y - msg.value; }
                }
            """.trimIndent() to 2

    fun contractWithExplicitNonPayableFallbackAndAPayableFunction() = """
                contract Test {
                    uint x;
                    uint y;
                    ${FALLBACK} external {
                        msg.sender.send(x+y);
                    }

                    function f() public payable returns (uint) { return x + y - msg.value; }
                }
            """.trimIndent() to 2

    fun contractWithExplicitNonPayableFallbackAndANonPayableFunction() = """
                contract Test {
                    uint x;
                    uint y;
                    ${FALLBACK} external {
                        msg.sender.send(x+y);
                    }

                    function f() public returns (uint) { return x + y; }
                }
            """.trimIndent() to 2

    fun withImmutable(solc: String) = """
        contract DummyIntImmutable {
                uint256 public ${IMMUTABLE(solc)} x;
                constructor(uint256 _x) public {
                        x = _x;
                }

                function foo() public returns (uint256) {
                        require (x == 1); // if we do not handle immutables correctly, x will be 0, result will be unsound
                        return 100/(x-1);
                }
        }
    """.trimIndent() to 3

}


