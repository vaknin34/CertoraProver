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

@file:Suppress("DEPRECATION") // will be cleared in CVL Rewrite

package analysis.icfg

import analysis.ip.*
import annotation.ScopedMatrix
import annotation.SolidityConfigMatrix
import annotation.SolidityVersion
import annotations.TestTags.EXPENSIVE
import bridge.*
import compiler.calculateHashFromCanonicalName
import compiler.calculateHashFromCanonicalNameBigInt
import config.ReportTypes
import datastructures.stdcollections.emptyList
import datastructures.stdcollections.listOf
import datastructures.stdcollections.mapOf
import decompiler.BMCRunner
import loaders.SceneTest
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Tag
import org.junit.jupiter.params.ParameterizedTest
import scene.SceneFactory
import scene.loader.SimpleProverContractLoader
import scene.source.IContractSourceFull
import spec.cvlast.*
import testing.StaticContractSource
import utils.parallelStream
import vc.data.CoreTACProgram
import vc.data.TACCmd
import verifier.CoreToCoreTransformer
import java.math.BigInteger
import java.util.stream.Collectors


// TODO CVL REWRITE : RE-ENABLE CER-1493
/*
@SolidityConfigMatrix(
    withHeaders = true,
    withOptimizeFlag = true,
    solidityVersion = [SolidityVersion.V6_10, SolidityVersion.V7_0, SolidityVersion.V6_12, SolidityVersion.V5_11, SolidityVersion.V7_6,
        SolidityVersion.V8_2, SolidityVersion.V8_11, SolidityVersion.V8_9]
)
@Tag(EXPENSIVE)
class InternalFunctionFinderTest : SceneTest {
    val UINT_SOLIDITY_TYPE = SolidityType("uint256", SourceTypeDescription.primitive("uint256"), arrayDims = emptyList())
    val UINT_DYNAMIC_ARRAY_SOLIDITY_TYPE = SolidityType("uint256", null, arrayDims = listOf(-1))
    private val theConstant = "0xf145740"

    private fun BigInteger.toHex() = "0x${this.toString(16)}"

    private operator fun BigInteger.plus(x: Int) = this + x.toBigInteger()

    private fun generateFinder(
        vararg argNames: String
    ) : String {
        return """
            assembly {
                mstore(${internalAnnotationMask.toHex()}, $theConstant)
                mstore(${internalAnnotationMask.plus(BigInteger.ONE).toHex()}, ${argNames.size})
                ${
                    argNames.withIndex().joinToString("\n") { (ind,nm) ->
                        "mstore(${(internalAnnotationMask + 4096 + ind).toHex()}, $nm)"
                    }
                }
            }
        """.trimIndent()
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testSimpleFunction(solc: String, optimize: Boolean, pragma: String) {

        val src = """
            $pragma
            contract Test {
                function test(uint256 x, uint256 y) public pure returns (uint256) {
                    uint256 a = simpleFunction(x);
                    uint256 b = simpleFunction(y);
                    return a + b;
                }

                function simpleFunction(uint256 x) internal pure returns (uint256) {
                    ${this.generateFinder("x")}
                    return x + x + 5;
                }
            }
        """.trimIndent()

        val finder = mapOf(
            theConstant to Method(
                "simpleFunction",
                fullArgs = listOf(UINT_SOLIDITY_TYPE),
                returns = listOf(UINT_SOLIDITY_TYPE),
                sighash = calculateHashFromCanonicalName("simpleFunction(uint256)"),
                paramNames = listOf("x")
            )
        )
        val expected = listOf(
            Expected(InternalMethodSignature.Named(CVLLocation.Empty(), FunctionReference(SolidityContract.Current, "simpleFunction"),
                params = listOf(CVLParam(CVLInbuiltSimpleTypes.uint.cvlType, "x")),
                res = listOf(CVLParam.Unnamed(CVLInbuiltSimpleTypes.uint.cvlType)), calculateHashFromCanonicalNameBigInt("simpleFunction(uint256)")
            ), 2, 1)

        )
        testFunctionFinder(src, solc, optimize, pragma, finder, expected)
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testNoArgs(solc: String, optimize: Boolean, pragma: String) {
        val src = """
            $pragma
            contract Test {
                uint256 x;

                function test() public returns (uint256) {
                    uint256 a = myGetX();
                    x = 5;
                    uint256 b = myGetX();
                    return a + b + myGetX();
                }

                function myGetX() internal view returns (uint256) {
                    ${generateFinder()}
                    return x;
                }
            }
        """.trimIndent()

        val finder = mapOf(
            theConstant to Method(
                "myGetX",
                fullArgs = listOf(),
                returns = listOf(UINT_SOLIDITY_TYPE),
                sighash = calculateHashFromCanonicalName("myGetX()"),
                paramNames = listOf()
            )
        )
        val expected = listOf(
            Expected(InternalMethodSignature.Named(CVLLocation.Empty(), FunctionReference(SolidityContract.Current, "myGetX"),
                params = listOf(),
                res = listOf(CVLParam.Unnamed(CVLInbuiltSimpleTypes.uint.cvlType)), calculateHashFromCanonicalNameBigInt("myGetX()")), 3, 1)
        )
        testFunctionFinder(src, solc, optimize, pragma, finder, expected)
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testTwoArrayArgs(solc: String, optimize: Boolean, pragma: String) {
        val src = """
            $pragma
            contract Test {
                uint256 state;

                function test(uint256[] calldata arr, address[] calldata addrs) external {
                    useArrays(arr, addrs);
                    address[] memory newArr;
                    if (state > arr.length) {
                        useArrays(arr, newArr);
                    }
                }

                function useArrays(uint256[] memory arr, address[] memory addrs) internal {
                    ${generateFinder("arr", "addrs")}
                    state = arr.length + addrs.length;
                }
            }
        """.trimIndent()

        val finder = mapOf(
            theConstant to Method(
                "useArrays",
                fullArgs = listOf(
                    UINT_DYNAMIC_ARRAY_SOLIDITY_TYPE,
                    SolidityType("address", typeDescription = null, arrayDims = listOf(-1))
                ),
                returns = listOf(),
                sighash = calculateHashFromCanonicalName("useArrays(uint256[],address[])"),
                paramNames = listOf("arr", "addrs")
            )
        )
        val expected = listOf(
            Expected(InternalMethodSignature.Named(CVLLocation.Empty(), FunctionReference(SolidityContract.Current, "useArrays"),
                params = listOf(CVLParam(CVLInbuiltSimpleTypes.EVMArray(CVLInbuiltSimpleTypes.uint, listOf(-1)).cvlType, "arr"),
                    CVLParam(CVLInbuiltSimpleTypes.EVMArray(CVLInbuiltSimpleTypes.address, listOf(-1)).cvlType, "addrs")),
                res = listOf(), calculateHashFromCanonicalNameBigInt("useArrays(uint256[],address[])")), 2, 1)
        )
        testFunctionFinder(src, solc, optimize, pragma, finder, expected)
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testTwoArrayArgs2(solc: String, optimize: Boolean, pragma: String) {
        val src = """
            $pragma
            contract Test {
                uint256 state;
                function test(uint256[] memory arr, address[] memory addrs) public {
                    useArrays(arr, addrs);
                    address[] memory newArr;
                    if (state > arr.length) {
                        useArrays(arr, newArr);
                    }
                }

                function useArrays(uint256[] memory arr, address[] memory addrs) internal {
                    ${generateFinder("arr", "addrs")}
                    state = arr.length + addrs.length;
                }
            }
        """.trimIndent()

        val finder = mapOf(
            theConstant to Method(
                "useArrays",
                fullArgs = listOf(
                    UINT_DYNAMIC_ARRAY_SOLIDITY_TYPE,
                    SolidityType("address", typeDescription = null, arrayDims = listOf(-1))
                ),
                returns = listOf(),
                sighash = calculateHashFromCanonicalName("useArrays(uint256[],address[])"),
                paramNames = listOf("arr", "addrs")
            )
        )
        val expected = listOf (
            Expected(InternalMethodSignature.Named(CVLLocation.Empty(), FunctionReference(SolidityContract.Current, "useArrays"),
            params = listOf(CVLParam(CVLInbuiltSimpleTypes.EVMArray(CVLInbuiltSimpleTypes.uint, listOf(-1)).cvlType, "arr"),
                CVLParam(CVLInbuiltSimpleTypes.EVMArray(CVLInbuiltSimpleTypes.address, listOf(-1)).cvlType, "addrs")),
            res = listOf(), calculateHashFromCanonicalNameBigInt("useArrays(uint256[],address[])")), 2, 1)
        )
        testFunctionFinder(src, solc, optimize, pragma, finder, expected)
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testReturnLocallyInitializedArray(solc: String, optimize: Boolean, pragma: String) {
        val src = """
            $pragma
            contract Test {
                function test(uint256 n) public returns (uint256) {
                    return returnsArray(n).length;
                }

                function returnsArray(uint256 n) internal returns (uint256[] memory) {
                    ${generateFinder("n")}
                    uint256[] memory ret = new uint256[](n);
                    return ret;
                }
            }
        """.trimIndent()

        val finder = mapOf(
            theConstant to Method(
                "returnsArray",
                fullArgs = listOf(UINT_SOLIDITY_TYPE),
                returns = listOf(UINT_DYNAMIC_ARRAY_SOLIDITY_TYPE),
                sighash = calculateHashFromCanonicalName("returnsArray(uint256)"),
                paramNames = listOf("n")
            )
        )
        val expected = listOf(
            Expected(InternalMethodSignature.Named(CVLLocation.Empty(), FunctionReference(SolidityContract.Current, "returnsArray"),
                params = listOf(CVLParam(CVLInbuiltSimpleTypes.uint.cvlType, "n")),
                res = listOf(CVLParam.Unnamed(CVLInbuiltSimpleTypes.EVMArray(CVLInbuiltSimpleTypes.uint, listOf(-1)).cvlType)),
                calculateHashFromCanonicalNameBigInt("returnsArray(uint256)")), 1, 1)
        )
        testFunctionFinder(src, solc, optimize, pragma, finder, expected)
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testReturnArrayFromState(solc: String, optimize: Boolean, pragma: String) {
        val src = """
            $pragma
            contract Test {
                uint256[] state;

                function test(uint256 n) public returns (uint256) {
                    uint256[] memory a = new uint256[](n * 2);
                    (uint256[] memory x, uint256[] memory y) = returnsArray(n, a);
                    return x.length + y.length;
                }

                function returnsArray(uint256 n, uint256[] memory local) internal returns (uint256[] memory, uint256[] memory) {
                    ${generateFinder("n", "local")}
                    uint256[] memory ret1 = state;
                    uint256[] memory ret2 = local;
                    return (ret1, ret2);
                }
            }
        """.trimIndent()
        val finder = mapOf(theConstant to Method("returnsArray",
            fullArgs = listOf(UINT_SOLIDITY_TYPE, UINT_DYNAMIC_ARRAY_SOLIDITY_TYPE),
            returns = listOf(UINT_DYNAMIC_ARRAY_SOLIDITY_TYPE, UINT_DYNAMIC_ARRAY_SOLIDITY_TYPE),
            sighash = calculateHashFromCanonicalName("returnsArray(uint256,uint256[])"),
            paramNames = listOf("n", "local"))
        )
        val expected = listOf(
            Expected(InternalMethodSignature.Named(CVLLocation.Empty(), FunctionReference(SolidityContract.Current, "returnsArray"),
                params = listOf(CVLParam(CVLInbuiltSimpleTypes.uint.cvlType, "n"),
                    CVLParam(CVLInbuiltSimpleTypes.EVMArray(CVLInbuiltSimpleTypes.uint, listOf(-1)).cvlType, "local")),
                res = listOf(CVLParam.Unnamed(CVLInbuiltSimpleTypes.EVMArray(CVLInbuiltSimpleTypes.uint, listOf(-1)).cvlType),
                    CVLParam.Unnamed(CVLInbuiltSimpleTypes.EVMArray(CVLInbuiltSimpleTypes.uint, listOf(-1)).cvlType)),
                calculateHashFromCanonicalNameBigInt("returnsArray(uint256,uint256[])")), 1, 1)
        )
        testFunctionFinder(src, solc, optimize, pragma, finder, expected)
    }

    data class Expected(val id: InternalMethodSignature, val occurrences: Int, val exitPoints: Int)

    private fun testFunctionFinder(
        src: String,
        solc: String,
        optimize: Boolean,
        pragma: String,
        finder: Map<String, Method>,
        expected: List<Expected>
    ) {
        println("Test Function Finder [solc: $solc], [optimize: $optimize], [pragma: $pragma]")
        val orig = StaticContractSource(solidityExec = solc, optimize = optimize, sourceCode = src)
        assertEquals(0, orig.runnerErrors.size)
        val withInternal = object : IContractSourceFull {
            override fun instances(): List<ContractInstanceInSDC> {
                return orig.instances().map {
                    if(it.name == "Test") {
                        it.copy(
                            internalFunctions = finder
                        )
                    } else {
                        it
                    }
                }
            }
        }
        val testScene = SceneFactory.getScene(withInternal, SimpleProverContractLoader)
        val functionFinder = testScene.getContract(NamedContractIdentifier("Test")).getMethods().single {
            it.name == "test"
        }
        val annotatedTest = functionFinder.code as CoreTACProgram
        expected.forEach { _expected ->
            val starts = annotatedTest.analysisCache.graph.commands.parallelStream().filter { lc ->
                        val cmd = lc.cmd
                        cmd is TACCmd.Simple.AnnotationCmd &&
                                cmd.annot.k == INTERNAL_FUNC_START &&
                                (cmd.annot.v as? InternalFuncStartAnnotation)?.methodSignature?.sighashInt == _expected.id.sighashInt
                    }.collect(Collectors.toList())
            // Number of occurrences
            assertEquals(_expected.occurrences, starts.size) {
                "Expected ${_expected.occurrences} occurrences of " +
                        "the function ${_expected.id} but instead got ${starts.size}"
            }

            // Number arguments at each occurrence
            starts.forEach { start ->
                val annot = (start.cmd as TACCmd.Simple.AnnotationCmd).annot.v
                        as InternalFuncStartAnnotation
                assertEquals(_expected.id.paramTypes.size, annot.args.size) {
                    "Expected ${_expected.id.paramTypes.size} arguments to the function " +
                            "${_expected.id} at $start but got ${annot.args.size}"
                }
            }

            // Now look at exits
            val exits = starts.associateWith { cmd ->
                val annot = (cmd.cmd as TACCmd.Simple.AnnotationCmd).annot.v
                        as InternalFuncStartAnnotation
                InternalFunctionExitFinder.getExits(annot.id, cmd.ptr, annotatedTest)
            }
            exits.forEach { (start, exits) ->
                // number exit points at each occurrence
                assertEquals(_expected.exitPoints, exits.size) {
                    "Expected ${_expected.exitPoints} exit points for " +
                            "function ${_expected.id} but got ${exits.size} for occurrence $start"
                }
                exits.forEach { exit ->
                    val annot = exit.cmd.annot.v as InternalFuncExitAnnotation
                    // number return variables
                    assertEquals(_expected.id.resType.flattenAndFilterCVLType.PureCVLType.Void().size, annot.rets.size) {
                        "Expected ${_expected.id.resType.flattenAndFilterCVLType.PureCVLType.Void().size} rets for " +
                                "function ${_expected.id} but got ${annot.rets.size} for occurrence ${start.ptr} at exit " +
                                "${exit.ptr}"
                    }
                }
            }
        }

    }
}
*/
