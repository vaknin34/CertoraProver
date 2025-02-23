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

package analysis

import analysis.pta.FlowPointsToInformation
import analysis.pta.TrivialPointsToInformation
import annotation.ScopedMatrix
import annotation.SolidityConfigMatrix
import annotation.SolidityVersion
import annotations.TestTags.EXPENSIVE
import loaders.SolidityContractTest
import loaders.runPTA
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Tag
import org.junit.jupiter.params.ParameterizedTest

@SolidityConfigMatrix(
        withHeaders = false,
        withOptimizeFlag = true,
        solidityVersion = [SolidityVersion.V6_6, SolidityVersion.V6_10, SolidityVersion.V7_0,
            SolidityVersion.V6_8, SolidityVersion.V8_2, SolidityVersion.V7_6, SolidityVersion.V8_11,
            SolidityVersion.V8_9, SolidityVersion.V8_13, SolidityVersion.V8_16]
)
@Tag(EXPENSIVE)
class TestABIV2Encoding : SolidityContractTest {

    @ParameterizedTest
    @ScopedMatrix
    fun testStringReturn(solc: String, optimize: Boolean) {
        val method = this.loadTestContractMethod("analysis/StringReturn.sol", solc, optimize)
        Assertions.assertTrue(runPTA(method) !is TrivialPointsToInformation)
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testPrimitiveArray(solc: String, optimize: Boolean) {
        val method = this.loadTestContractMethod("analysis/ArrayArgument.sol", solc, optimize)
        Assertions.assertTrue(runPTA(method) !is TrivialPointsToInformation)
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testAddressArray(solc: String, optimize: Boolean) {
        val method = this.loadTestContractMethod("analysis/ArrayAddressArgument.sol", solc, optimize = optimize)
        Assertions.assertTrue(runPTA(method) !is TrivialPointsToInformation)

    }


    @ParameterizedTest
    @ScopedMatrix
    fun testStringArgAndParameter(solc: String, optimize: Boolean) {
        val method = this.loadTestContractMethod("analysis/StringArgument.sol", solc, optimize = optimize)
        val pta = runPTA(method)
        Assertions.assertTrue(pta !is TrivialPointsToInformation)
        Assertions.assertTrue(pta !is TrivialPointsToInformation) {
            "Failed on $solc & $optimize"
        }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testCalldataStringArgAndParameter(solc: String, optimize: Boolean) {
        val method = this.loadTestContractMethod("analysis/StringArgumentCalldata.sol", solc, optimize = optimize)
        val pta = runPTA(method)
        Assertions.assertTrue(pta !is TrivialPointsToInformation)
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testEncodePacked(solc: String, optimize: Boolean) {
        val method = this.loadTestContractMethod("analysis/EncodePacked.sol", solc, optimize)
        val pta = runPTA(method)
        Assertions.assertTrue(pta !is TrivialPointsToInformation)
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testEncodePackedStorageString(solc: String, optimize: Boolean) {
        val method = this.loadTestContractMethod("analysis/StorageStringPackedEncode.sol", solc, optimize = optimize)
        val pta = runPTA(method)
        Assertions.assertTrue(pta !is TrivialPointsToInformation)
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testStructArrayArgument(solc: String, optimize: Boolean) {
        val method = this.loadTestContractMethod("analysis/StructArrayArgument.sol", solc, optimize = optimize)
        val pta = runPTA(method)
        Assertions.assertTrue(pta !is TrivialPointsToInformation) {
            "$solc with opt: $optimize"
        }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testDoubleArray(solc: String, optimize: Boolean) {
        val innerArrayType = listOf(
                "bytes",
                "uint[]",
                "address[]"
        )
        for(ty in innerArrayType) {
            val contract = """
            pragma experimental ABIEncoderV2;

            contract Test {
               function test(uint l, uint l2) public returns (uint) {
                   $ty[] memory input = new $ty[](l);
                   input[0] = new $ty(l2);
                   return this.extCall(input);
               }

               function extCall($ty[] memory d) public returns (uint) {
                   return d.length;
               }
            }
        """.trimIndent()
            val method = this.loadTestMethod(contract, solc, optimize)
            val pta = runPTA(method)
            Assertions.assertTrue(pta !is TrivialPointsToInformation) {
                "Failed with type $ty"
            }
        }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testDoubleArrayAllEmpty(solc: String, optimize: Boolean) {
        val innerArrayType = listOf(
                "bytes",
                "uint[]",
                "address[]"
        )
        for(ty in innerArrayType) {
            val contract = """
            pragma experimental ABIEncoderV2;

            contract Test {
               function test(uint l, uint l2) public returns (uint) {
                   $ty[] memory input = new $ty[](l);
                   return this.extCall(input);
               }

               function extCall($ty[] memory d) public returns (uint) {
                   return d.length;
               }
            }
        """.trimIndent()
            val method = this.loadTestMethod(contract, solc, optimize)
            val pta = runPTA(method)
            Assertions.assertTrue(pta !is TrivialPointsToInformation) {
                "Failed with type $ty, $solc & $optimize"
            }
        }
    }

    @ScopedMatrix
    @ParameterizedTest
    fun testStructWithArrayReturn(solc: String, opt: Boolean) {
        val method = this.loadTestContractMethod("analysis/StructWithArrayReturn.sol", solc, optimize = opt)
        val pta = runPTA(method)
        Assertions.assertTrue(pta !is TrivialPointsToInformation)
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testStaticArrayArguments(solc: String, opt: Boolean) {
        val staticType = listOf(
                Triple("uint", "", { x: String ->
                    x
                }),
                Triple("uint[]", "", { x: String ->
                    "$x[0]"
                }),
                Triple("bytes", "", { x: String ->
                    "$x.length"
                }),
                Triple("address[]", "", { x: String ->
                    "uint(uint160($x[0]))"
                }),
                Triple("Yolo", """
                    struct Yolo {
                       uint a;
                       uint b;
                       bytes bar;
                       address[] foo;
                    }
                """.trimIndent(), { x: String ->
                    "$x.a"
                })
        )

        for((nestedType, decl, extract) in staticType) {
            val contract = """
                pragma experimental ABIEncoderV2;

                contract Test {
                   $decl

                   function test($nestedType[3] memory input) public returns ($nestedType[3] memory) {
                      uint index = ${extract("input[0]")};
                      input[index] = input[0];
                      return input;
                   }
                }
            """.trimIndent()
            val method = this.loadTestMethod(contract, solc, opt)
            val pta = runPTA(method)
            Assertions.assertTrue(pta is FlowPointsToInformation) {
                "Failed on $solc, $opt, $nestedType"
            }
        }
    }
}
