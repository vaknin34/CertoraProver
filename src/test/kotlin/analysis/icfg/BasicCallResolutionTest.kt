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

package analysis.icfg

import annotation.ScopedVersions
import annotation.SolidityVersion
import annotation.SolidityVersions
import decompiler.BMCRunner
import loaders.SoliditySceneTest
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import scene.ITACMethod
import spec.cvlast.SolidityContract
import vc.data.CoreTACProgram
import java.math.BigInteger

@SolidityVersions([SolidityVersion.ANY_5,
    SolidityVersion.V6_10,
    SolidityVersion.V6_12,
    SolidityVersion.V7_0,
    SolidityVersion.V7_6,
    SolidityVersion.V8_2,
    SolidityVersion.V8_9,
    SolidityVersion.V8_11,
    SolidityVersion.V8_13,
    SolidityVersion.V8_16,
    SolidityVersion.V8_28
])
class BasicCallResolutionTest : SoliditySceneTest  {
    @ParameterizedTest
    @ScopedVersions
    fun simpleCall(solc: String) {
        val (_, results) = this.runPipeline("icfg/SimpleCall.sol", solc)
        assertSingleResolution(results, 0x207b6d64)
    }

    @ParameterizedTest
    @ScopedVersions
    fun noArgCall(solc: String) {
        val (_, results) = this.runPipeline("icfg/NoArgCall.sol", solc)
        Assertions.assertTrue(results.sigResolution.resolution.size == 1)
        assertSingleResolution(results, 0x2b9e1919)
    }

    @ParameterizedTest
    @ScopedVersions
    fun rawBytesCall(solc: String) {
        val (_, results) = this.runPipeline("icfg/RawCall.sol", solc)
        assertSingleResolution(results, "8c436faf")
    }

    @ParameterizedTest
    @ScopedVersions
    fun dynamicRawBytesCall(solc: String) {
        val (_, results) = this.runPipeline("icfg/RawCallWithDynamic.sol", solc)
        assertSingleResolution(results, "4fa61016")
    }

    @ParameterizedTest
    @ScopedVersions
    fun directCallWithDynamic(solc: String) {
        val (_, results) = this.runPipeline("icfg/DirectCallWithDynamic.sol", solc)
        assertSingleResolution(results, "8ba9eabd")
    }

    @ParameterizedTest
    @ScopedVersions
    fun encodedWithSelectorAndDynamic(solc: String) {
        val (_, results) = this.runPipeline("icfg/SelectorResolutionWithDynamic.sol", solc)
        assertSingleResolution(results, "d0a10260")
    }

    @ParameterizedTest
    @ScopedVersions
    fun twoSequencedCallsTest(solc: String) {
        val (_, results) = this.runPipeline("icfg/TwoSequentialCalls.sol", solc)
        Assertions.assertEquals(2, results.sigResolution.resolution.size)
        val ordered = results.sigResolution.resolution.entries.sortedBy {
            // roughly in program order. This isn't safe in general, but fine in a test (imho)
            it.key.block.origStartPc
        }
        Assertions.assertEquals(1, ordered.first().value.size)
        Assertions.assertEquals(BigInteger("3462755a", 16), ordered.first().value.first())
        Assertions.assertEquals(1, ordered[1].value.size)
        Assertions.assertEquals(BigInteger("ad181a2f", 16), ordered[1].value.first())

        val firstCall = ordered.first().key
        Assertions.assertTrue(firstCall in results.callInputResolution.resolution)
        val firstInput = results.callInputResolution.resolution[firstCall]!!
        Assertions.assertEquals(2, firstInput.rangeToDecomposedArg.size)

        val secondCall = ordered[1].key
        Assertions.assertTrue(secondCall in results.callInputResolution.resolution)
        val secondInput = results.callInputResolution.resolution[secondCall]!!
        Assertions.assertEquals(1, secondInput.rangeToDecomposedArg.size)
    }

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V6_10, SolidityVersion.V7_0])
    fun testEncodeSelector(solc: String) {
        val (_, results) = this.runPipeline("icfg/EncodeWithSelector.sol", solc)
        assertSingleResolution(results, 0x76c232a3)
    }

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V6_10, SolidityVersion.V7_0])
    fun testCalldataBytesArgument(solc: String) {
        val (_, results) = this.runPipeline("icfg/CallWithCalldataBytes.sol", solc)
        assertSingleResolution(results, "afafb797")
    }

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V6_10, SolidityVersion.V7_0])
    fun testEncodeSelectorWithPragma(solc: String) {
        val (_, results) = this.runPipeline("icfg/EncodeWithSelectorPragma.sol", solc)
        assertSingleResolution(results, 0x76c232a3)
    }

    private fun assertSingleResolution(results: CallGraphBuilder.AnalysisResults, expectedSig: Int) {
        val bigSig = expectedSig.toBigInteger()
        assertSingleResolution(results, bigSig)
    }

    private fun assertSingleResolution(results: CallGraphBuilder.AnalysisResults, sigString: String) {
        assertSingleResolution(results, BigInteger(sigString, 16))
    }

    private fun assertSingleResolution(results: CallGraphBuilder.AnalysisResults, bigSig: BigInteger) {
        Assertions.assertTrue(results.sigResolution.resolution.isNotEmpty())
        Assertions.assertTrue(results.sigResolution.resolution.size == 1)
        val possibleSigs = results.sigResolution.resolution.entries.first().value
        Assertions.assertTrue(possibleSigs.size == 1)
        Assertions.assertEquals(bigSig, possibleSigs.first())
    }

    private fun runPipeline(path: String, solc: String): Pair<ITACMethod, CallGraphBuilder.AnalysisResults> {
        val scene = this.loadScene(path, solc)
        scene.mapContractMethodsInPlace("unrolling") { _, m ->
            m.code = BMCRunner(1, m.code as CoreTACProgram).bmcUnroll()
        }
        val m = scene.getContractOrNull(SolidityContract("Test"))?.getMethods()?.firstOrNull {
            it.name == "test"
        } ?: Assertions.fail("Could not find Test-test in $path")
        val res = CallGraphBuilder.doSigAnalysis(m) ?: Assertions.fail("Call graph analysis failed")
        return m to res
    }
}
