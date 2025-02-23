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

package analysis.abi

import analysis.maybeAnnotation
import analysis.pta.abi.ABIDecodeComplete
import analysis.pta.abi.DecoderAnalysis
import annotation.ScopedMatrix
import config.Config
import extension.DependentPair
import extension.setTo
import loaders.SingleMethodTest
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import vc.data.TACCmd
import vc.data.TACKeyword
import java.math.BigInteger

abstract class DecoderTest : SingleMethodTest, AbiPathBuilder {
    open val abiHeader: String = "pragma experimental ABIEncoderV2;"

    @ParameterizedTest
    @ScopedMatrix
    fun basicArrayType(solc: String,  optimize: Boolean) {
        val types = listOf(
                "bytes",
                "uint[]",
                "address[]"
        )
        for(ty in types) {
            val source = """
                    $abiHeader

                    contract Test {
                        function test($ty memory a) public returns (uint) {
                           return a.length;
                        }
                    }
            """.trimIndent()
            if(ty == "bytes" && solc == "solc7.6") {
                // lol
                continue
            }
            runPipeline(source, solc, optimize, listOf(
                AbiPathBuilder.BufferAccessPathBuilder(BigInteger.ZERO).deref.path
            )) {
                "Failed on $ty, $solc, $optimize"
            }
        }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testBufferDecode(solc: String, optimize: Boolean) {
        val src = """
            $abiHeader

            contract Test {
            	struct YeetStruct {
                    uint a;
                    uint b;
                }
                function test(bytes memory b) public returns (uint) {
                    YeetStruct[] memory x = abi.decode(b, (YeetStruct[]));
                    return x.length;
                }

            }
        """.trimIndent()
        val abis = this.loadTestGraph(
            src,
            solc,
            optimize
        ).commands.mapNotNull { it.maybeAnnotation(ABIDecodeComplete.META_KEY) }

        Assertions.assertTrue(
            abis.any { p ->
                val sourcePath = AbiPathBuilder.BufferAccessPathBuilder(BigInteger.ZERO).deref.path
                val sourceBuffer = TACKeyword.CALLDATA.toVar()
                p.sourceBuffer != sourceBuffer && p.sourcePath == sourcePath
            }
        )
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testIndexedDecode(solc: String, optimize: Boolean) {
        val src = """
            $abiHeader

            contract Test {
                function test(uint i, uint[][] calldata y) external returns (uint) {
                    uint[] memory yeet = y[i];
                    return yeet.length;
                }
            }
        """.trimIndent()
        this.runPipeline(src, solc = solc, optimize = optimize, expected = listOf(
                32.toBuilder().deref[AbiPathBuilder.Elem].at(0).deref.path
        )) {
            "failed on $solc and opt = $optimize"
        }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun twoArrayTypes(solc: String,  optimize: Boolean) {
        val types = listOf(
                "uint[]",
                "address[]",
                "bytes"
        )
        for(ty1 in types) {
            for(ty2 in types) {
                val source = """
                $abiHeader

                contract Test {
                    function test($ty1 memory a, $ty2 memory b) public returns (uint) {
                       return a.length + b.length;
                    }
                }
            """.trimIndent()
                if (ty1 == "bytes" && solc == "solc7.6") {
                    // lol
                    continue
                }
                runPipeline(source, solc, optimize, listOf(
                        32.toBuilder().deref.path,
                        0.toBuilder().deref.path,
                )) {
                    "Failed on $ty1 & $ty2, $solc, $optimize"
                }
            }
        }
    }

    @ScopedMatrix
    @ParameterizedTest
    fun testRootedTuple(solc: String, optimize: Boolean) {
        val source = """
            $abiHeader

            contract Test {
                function test(uint[3][5] memory f) public returns (uint) {
                    return f[0][0];
                }
            }
        """.trimIndent()

        runPipeline(source, solc, optimize, listOf(
                0.toRootOffset()
        )) {
            "Failed on $solc $optimize"
        }
    }

    @ScopedMatrix
    @ParameterizedTest
    fun testComplexStruct(solc: String, optimize: Boolean) {
        val source = """
            $abiHeader

            contract Test {
                struct A {
                   uint a;
                   uint[3][5] b;
                   uint[][2] c;
                }
                function test(A memory f) public returns (uint) {
                    return f.a;
                }
            }
        """.trimIndent()
        runPipeline(source, solc, optimize, listOf(
                0.toBuilder().deref.path
        )) {
            "Failed on $solc $optimize"
        }
    }

    @ScopedMatrix
    @ParameterizedTest
    fun testDoublyNestedArrays(solc: String, optimize: Boolean) {
        val ty = listOf(
                "uint[]",
                "bytes",
                "address[]"
        )
        for(t in ty) {
            val source = """
            $abiHeader

            contract Test {
                function test($t[] memory f) public returns (uint) {
                    return f.length;
                }
            }
            """.trimIndent()
            runPipeline(source, solc, optimize, listOf(
                    0.toBuilder().deref.path
            )) {
                "Failed on $solc, $optimize, and type $t"
            }
        }
    }


    private fun runPipeline(source: String, solc: String, optimize: Boolean, expected: Collection<DecoderAnalysis.BufferAccessPath>, message: () -> String) {
        val d = this.loadTestGraph(source, solc, optimize)
        val seen = mutableSetOf<DecoderAnalysis.BufferAccessPath>()
        val paths = d.commands.mapNotNull { it.maybeAnnotation(ABIDecodeComplete.META_KEY)?.sourcePath }
        for(p in paths) {
            val j = expected.mapNotNull {
                it.joinOrNull(p)
            }
            if(j.isEmpty()) {
                Assertions.fail<Nothing>("Failed to find output $p in expected paths $expected (${message.invoke()})")
            }
            seen.addAll(j)
        }
        val remaining = expected.toSet() - seen
        Assertions.assertEquals(0, remaining.size) {
            "Expected to have seen all paths in $expected, remaining: $remaining (${message()})"
        }
    }

    companion object {
        @JvmStatic
        fun certoraConfig() : List<DependentPair<*>> = listOf(
            Config.EnabledABIAnalysis setTo true
        )
    }
}
