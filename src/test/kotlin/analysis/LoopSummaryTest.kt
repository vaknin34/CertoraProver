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

import analysis.pta.LoopCopyAnalysis
import annotation.SolidityVersion
import annotations.TestTags.EXPENSIVE
import extension.IgnoreZ3TimeoutErrors
import loaders.SingleMethodTest
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.extension.ExtendWith
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import scene.ITACMethod
import vc.data.CoreTACProgram
import vc.data.TACCmd
import java.util.stream.Stream

@ExtendWith(IgnoreZ3TimeoutErrors::class)
@Tag(EXPENSIVE)
class LoopSummaryTest : SingleMethodTest {

    @ParameterizedTest
    @MethodSource("testMatrix")
    fun copyToCallBuffer(solc: String, header: String, type: String, optimize: Boolean) {
        val contractSource = """
            $header

            contract Test {
                 function other($type memory o) public { }
                 function test(uint len) public {
                   $type memory x = new $type(len);
                   this.other(x);
                 }
            }
        """.trimIndent()
        val meth = this.loadTestMethod(contractSource, solc, optimize)
        val loopSummaries = getLoopSummaries(meth)
        Assertions.assertEquals(1, loopSummaries.size, "With $solc and pragma [$header] and optimize $optimize for type $type, got ${loopSummaries.size}")
    }

    @ParameterizedTest
    @MethodSource("headerVersionMatrix")
    fun copyToRawCall(solc: String, header: String, optimize: Boolean) {
        val contractSource = """
            $header

            contract Test {
               function test(uint l) public {
                  bytes memory x = new bytes(l);
                  address(this).call(x);
               }
            }
        """.trimIndent()

        val meth = this.loadTestMethod(contractSource, solc, optimize)
        val loopSummaries = getLoopSummaries(meth)
        Assertions.assertEquals(1, loopSummaries.size) {
            "With $solc and header [$header]"
        }
    }

    private fun getLoopSummaries(meth: ITACMethod): List<LoopCopyAnalysis.LoopCopySummary> {
        return (meth.code as CoreTACProgram).code.values.flatMap {
            it.filterIsInstance<TACCmd.Simple.SummaryCmd>()
        }.mapNotNull {
            it.summ as? LoopCopyAnalysis.LoopCopySummary
        }
    }

    @ParameterizedTest
    @MethodSource("testMatrix")
    fun testPackedCopyLoop(solc: String, header: String, type: String, optimize: Boolean) {
        val contractSource = """
            $header

            contract Test {
                function test(uint l) public returns (uint) {
                   $type memory z = new $type(l);
                   bytes memory x = abi.encodePacked(z, z);
                   return x.length;
                }
            }
        """.trimIndent()
        val meth = this.loadTestMethod(contractSource, solc, optimize)
        Assertions.assertEquals(2, getLoopSummaries(meth).size) {
            "Failed summary on $solc with header [$header] and type $type"
        }
    }

    companion object {
        @JvmStatic
        fun testMatrix(): Stream<Arguments> {
            return headerVersionGenerator() { ver, pragma, opt ->
                    listOf("uint[]", "bytes", "address[]").map {
                        Arguments.of(ver, pragma, it, opt)
                    }
            }.stream()
        }

        private fun headerVersionGenerator(f: (String, String, Boolean) -> List<Arguments>): List<Arguments> {
            return listOf(SolidityVersion.ANY_5, SolidityVersion.V7_0, SolidityVersion.V6_10, SolidityVersion.V6_1, SolidityVersion.V7_6,
                SolidityVersion.V8_2, SolidityVersion.V8_9, SolidityVersion.V8_13, SolidityVersion.V8_11, SolidityVersion.V8_16).flatMap { ver ->
                listOf("pragma experimental ABIEncoderV2;", "").flatMap { pragma ->
                    listOf(true, false).flatMap { opt ->
                        f(ver.compilerName(), pragma, opt)
                    }
                }
            }
        }

        @JvmStatic
        fun headerVersionMatrix() : Stream<Arguments> {
            return headerVersionGenerator { ver, prag, opt ->
                listOf(Arguments.of(ver, prag, opt))
            }.stream()
        }
    }

}
