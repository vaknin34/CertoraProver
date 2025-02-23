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

import analysis.icfg.ExtCallSummarization
import analysis.icfg.ScratchByteRange
import annotation.ScopedVersions
import annotation.SolidityVersion
import annotation.SolidityVersions
import annotations.TestTags
import decompiler.BMCRunner
import instrumentation.calls.CalldataEncoding
import loaders.SoliditySceneTest
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Tag
import org.junit.jupiter.params.ParameterizedTest
import scene.IScene
import scene.ITACMethod
import scene.Scene
import spec.cvlast.SolidityContract
import vc.data.*
import vc.data.TACMeta.IS_CALLDATA
import java.math.BigInteger

@Tag(TestTags.EXPENSIVE)
@SolidityVersions([SolidityVersion.V6_10])
class CalldataScalarizationTest : SoliditySceneTest {

    @ScopedVersions
    @ParameterizedTest
    fun callWithMemoryArrayArg(solc: String) {
        val scene = getSceneWithUnrolling("analysis/CalldataWithArrayScalarization.sol", solc)
        val resolvedTestArrayMethod = this.getMethodWithResolvedCalls(
            scene,
            "CalldataWithArrayScalarization",
            "testArray"
        )
        val expectedInputDecomp = ExpectedArgDecomposition.atLeast(
            ScratchByteRange(BigInteger.ZERO, 3.toBigInteger()), // first four bytes
            ScratchByteRange(4.toBigInteger(), 35.toBigInteger()), // uint256
            ScratchByteRange(36.toBigInteger(), 67.toBigInteger()), // offset to array base
            ScratchByteRange(68.toBigInteger(), 99.toBigInteger()), // uint256
            ScratchByteRange(100.toBigInteger(), 131.toBigInteger()) // array base (its length)
        )
        assertInputArgDecompSuccess(
            resolvedTestArrayMethod.second.first(),
            expectedInputDecomp,
            100.toBigInteger() /* 3 args (3*32) + first 4 bytes*/
        )

        this.assertCalldataScalarization(
            resolvedTestArrayMethod.first,
            setOf(4.toBigInteger(), 36.toBigInteger())
        )

        this.assertCalldataScalarization(
            getMethodFromScene(scene, "CalldataWithArrayScalarization", "funWithMemArray"),
            setOf(4.toBigInteger(), 36.toBigInteger(), 68.toBigInteger())
        )
    }

    @ScopedVersions
    @ParameterizedTest
    fun callWithTwoArrays(solc: String) {
        val scene = getSceneWithUnrolling("analysis/CalldataWithArrayScalarization.sol", solc)
        val resolvedTestArrayMethod = this.getMethodWithResolvedCalls(
            scene,
            "CalldataWithArrayScalarization",
            "testTwoArrays"
        )
        val expectedInputDecomp = ExpectedArgDecomposition.atLeast(
            ScratchByteRange(BigInteger.ZERO, 3.toBigInteger()), // first four bytes
            ScratchByteRange(4.toBigInteger(), 35.toBigInteger()), // bool arg
            ScratchByteRange(36.toBigInteger(), 67.toBigInteger()), // array1 offset to base
            ScratchByteRange(68.toBigInteger(), 99.toBigInteger()), // array2 offset to base
            ScratchByteRange(100.toBigInteger(), 131.toBigInteger()), // uint256 arg
            ScratchByteRange(132.toBigInteger(), 163.toBigInteger()) // base of array1 (its length)
        )
        assertInputArgDecompSuccess(
            resolvedTestArrayMethod.second.first(),
            expectedInputDecomp,
            132.toBigInteger() /* 4 args (4*32) + first 4 bytes*/
        )

        this.assertCalldataScalarization(
            resolvedTestArrayMethod.first,
            setOf(4.toBigInteger(), 36.toBigInteger())
        )

        this.assertCalldataScalarization(
            getMethodFromScene(scene, "CalldataWithArrayScalarization", "funWithTwoArrays"),
            setOf(
                4.toBigInteger(),
                36.toBigInteger(),
                68.toBigInteger(),
                100.toBigInteger()
            )
        )
    }


    @ScopedVersions
    @ParameterizedTest
    fun callWithStaticValueTypes(solc: String) {
        val scene = getSceneWithUnrolling("analysis/CalldataWithArrayScalarization.sol", solc)
        val resolvedTestMethod = this.getMethodWithResolvedCalls(
            scene,
            "CalldataWithArrayScalarization",
            "testOnlyStaticValueTypes"
        )
        val expectedInputDecomp = ExpectedArgDecomposition.exact(
            ScratchByteRange(BigInteger.ZERO, 3.toBigInteger()), // first four bytes
            ScratchByteRange(4.toBigInteger(), 35.toBigInteger()), // bool arg
            ScratchByteRange(36.toBigInteger(), 67.toBigInteger()), // uint256 offset to base
            ScratchByteRange(68.toBigInteger(), 99.toBigInteger()) // uint8 offset to base
        )
        assertInputArgDecompSuccess(
            resolvedTestMethod.second.first(),
            expectedInputDecomp,
            100.toBigInteger() /* 3 args (3*32) + first 4 bytes*/
        )

        this.assertCalldataScalarization(
            resolvedTestMethod.first,
            setOf(4.toBigInteger(), 36.toBigInteger(), 68.toBigInteger())
        )

        this.assertCalldataScalarization(
            getMethodFromScene(scene, "CalldataWithArrayScalarization", "funWithStaticValueTypes"),
            setOf(
                4.toBigInteger(),
                36.toBigInteger(),
                68.toBigInteger()
            )
        )
    }

    /**
     *
     *
     *
     *
     *
     * Private methods
     *
     *
     *
     *
     *
     */
    private fun getSceneWithUnrolling(@Suppress("SameParameterValue") path: String, solc: String): Scene =
        this.loadScene(path, solc).apply {
            this.mapContractMethodsInPlace("unrolling") { _, m ->
                m.code = BMCRunner(4, m.code as CoreTACProgram).bmcUnroll()
            }
            this.mapContractMethodsInPlace("resolve") { iScene: IScene, method: ITACMethod ->
                ExtCallSummarization.annotateCallsAndReturns(scene = iScene, method = method)
            }
        }


    private fun getMethodFromScene(
        scene: Scene, contractName: String,
        methodName: String
    ) = scene.getContractOrNull(SolidityContract(contractName))?.getMethods()?.firstOrNull {
        it.name == methodName
    } ?: Assertions.fail("Could not find ${contractName}-${methodName} in $scene")

    private fun getMethodWithResolvedCalls(
        scene: Scene,
        @Suppress("SameParameterValue") contractName: String,
        methodName: String
    ): Pair<ITACMethod, List<CallSummary>> {
        val method = this.getMethodFromScene(scene, contractName, methodName)
        return method to (method.code as CoreTACProgram).analysisCache.graph.commands.mapNotNull {
            it.snarrowOrNull<CallSummary>()
        }.toList()
    }

    private data class ExpectedArgDecomposition(
        val scratchByteRanges: Set<ScratchByteRange>,
        val compareOp: (Set<ScratchByteRange>, Set<ScratchByteRange>) -> Boolean
    ) {
        companion object {
            fun atLeast(vararg scratchByteRanges: ScratchByteRange) =
                ExpectedArgDecomposition(scratchByteRanges.toSet()) { a, b -> a.containsAll(b) }

            fun exact(vararg scratchByteRanges: ScratchByteRange) =
                ExpectedArgDecomposition(scratchByteRanges.toSet()) { a, b -> a == b }
        }
    }

    private fun assertInputArgDecompSuccess(
        callSummary: CallSummary,
        expectedArgDecomposition: ExpectedArgDecomposition,
        inputSizeLb: BigInteger
    ) {
        val inputResolution = callSummary.callConvention.input
        Assertions.assertTrue(
            expectedArgDecomposition.compareOp(
                inputResolution.rangeToDecomposedArg.keys,
                expectedArgDecomposition.scratchByteRanges
            )
        )

        inputResolution.inputSizeLowerBound?.let { Assertions.assertTrue(it >= inputSizeLb) }
    }


    private fun assertCalldataScalarization(method: ITACMethod, expectedScalarizedOffsets: Set<BigInteger>) {
        val calldataScalarOffsets = mutableSetOf<BigInteger>()
        (method.code as CoreTACProgram).analysisCache.graph.commands.forEach { ltacCmd ->
            when (val c = ltacCmd.cmd) {
                is TACCmd.Simple.AssigningCmd.AssignExpCmd -> {
                    val rhsVar = c.rhs.getAs<TACExpr.Sym.Var>()?.s
                    if (rhsVar?.meta?.containsKey(IS_CALLDATA) == true) {
                        Assertions.assertTrue(rhsVar.meta.find(TACMeta.WORDMAP_KEY) != null)
                        val offset = rhsVar.meta.find(TACMeta.WORDMAP_KEY)!!
                        calldataScalarOffsets.add(offset)
                    }
                }
                else -> {}
            }
        }
        if ((method.calldataEncoding as CalldataEncoding).valueTypesArgsOnly) {
            Assertions.assertEquals(expectedScalarizedOffsets, calldataScalarOffsets)
        } else {
            Assertions.assertTrue(calldataScalarOffsets.containsAll(expectedScalarizedOffsets)) {
                "Missing: ${expectedScalarizedOffsets - calldataScalarOffsets}"
            }
        }
    }
}
