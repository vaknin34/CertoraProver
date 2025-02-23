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

package normalizer

import analysis.CmdPointer
import analysis.icfg.ExtCallSummarization
import cache.utils.ObjectSerialization
import decompiler.BMCRunner
import instrumentation.transformers.CodeRemapper
import loaders.SolidityContractTest
import loaders.SoliditySceneTest
import normalizer.CanonicalTranslationTableTest.Companion.GLOBAL_KEYWORDS
import org.junit.jupiter.api.Assertions
import parallel.ParallelPool
import parallel.Scheduler.compute
import parallel.forkEvery
import parallel.pcompute
import scene.IScene
import scene.ITACMethod
import scene.Scene
import tac.CallId
import tac.MetaKey
import tac.NBId
import utils.*
import vc.data.*
import vc.data.tacexprutil.QuantDefaultTACExprTransformer
import java.io.ByteArrayInputStream
import java.io.ByteArrayOutputStream
import java.math.BigInteger
import kotlin.math.absoluteValue
import kotlin.random.Random
import kotlin.reflect.KClass
import kotlin.reflect.full.primaryConstructor


class Randomizer(val r: Random) {
    fun nextInt(until: Int? = null) = synchronized(r) {
        (until?.let { r.nextInt(it) } ?: r.nextInt()).absoluteValue
    }

    fun <T> randFromCollection(l: List<T>): Pair<Int, T> {
        val index = nextInt() % l.size
        return index to l[index]
    }

    fun randomNBIdField(): NBIdFieldSelector = synchronized(r) {
        val (_, field) = randFromCollection(NBIdFieldSelector.values().toList())
        return field
    }

    fun fork() = Randomizer(Random(nextInt()))
}

enum class NBIdFieldSelector {
    // If one TAC program is obtained from another via a transformation of these fields,
    // then the digest is preserved. This is because since canonicalization overwrites these values
    // with the same value, which is determined by the nbid's position in the canonicalization DFS scan
    // See BlockIdentifier.toCanon
    ORIG_START_PC,
    CALLEE_IDX,
    FRESH_COPY,

    // Digest is NOT preserved when these fields are transformed. Again, see BlockIdentifier.toCanon
    TOP_OF_STACK_VALUE,
    STK_TOP;

    fun modificationShouldPreserveDigest(method: CoreTACProgram, oldValue: Int): Boolean = when (this) {
        CALLEE_IDX, FRESH_COPY -> true
        TOP_OF_STACK_VALUE, STK_TOP -> false
        // if none of the modified `origStartPc` are from the decompiler than mutation should not affect digest
        ORIG_START_PC -> method.code.keys.asSequence().filter { it.origStartPc == oldValue }
            .all { !it.fromDecompiler() }
    }

    fun get(nbid: NBId): Int = when (this) {
        ORIG_START_PC -> nbid.origStartPc
        CALLEE_IDX -> nbid.calleeIdx
        FRESH_COPY -> nbid.freshCopy
        TOP_OF_STACK_VALUE -> nbid.topOfStackValue
        STK_TOP -> nbid.stkTop
    }

    fun maybeModifyField(nbid: NBId, oldValue: Int, newValue: Int): NBId =
        if (get(nbid) != oldValue) {
            nbid
        } else when (this) {
            ORIG_START_PC -> nbid.copy(origStartPc = newValue)
            TOP_OF_STACK_VALUE -> nbid.copy(topOfStackValue = newValue)
            CALLEE_IDX -> nbid.copy(calleeIdx = newValue)
            FRESH_COPY -> nbid.copy(freshCopy = newValue)
            STK_TOP -> nbid.copy(stkTop = newValue)
        }
}

/**
 * Default code mapper that maps it to itself
 **/
fun <T> buildCodeRemapper(
    blockRemapper: (NBId, (CallId) -> CallId, CodeRemapper.BlockRemappingStrategy.RemappingContext, T) -> NBId = { nbId, _, _, _ -> nbId },
    idRemapper: (T) -> (Any, Int, () -> Int) -> Int = { { _, id, _ -> id } },
    callIndexStrategy: (T, callIndex: CallId, computeFreshId: (CallId) -> CallId) -> CallId = { _, idx, _ -> idx },
    variableMapper: (T, TACSymbol.Var) -> TACSymbol.Var = { _, v -> v },
) = CodeRemapper(blockRemapper, idRemapper, callIndexStrategy, variableMapper)

class InconsistentDigestError(path: String, digests: List<String>) : Exception("$path: different digests($digests)", null)

open class CanonicalTranslationTableTest : SolidityContractTest, SoliditySceneTest {
    companion object {
        val GLOBAL_KEYWORDS = CanonicalTranslationTable.GLOBAL_KEYWORDS
    }
    private fun testConsistentDigest(solc: String, optimize: Boolean, vararg paths: String, numberOfCompiles: Int = 2) {
        val testRepetitions = 5
        val theTest = paths.toList().forkEvery { path ->
            (0 until numberOfCompiles).forkEvery {
                compute { loadTestContractMethod(path, solc, optimize) }
            }.pcompute().map { it.map { method -> (method.code as CoreTACProgram) } }.bind { methods ->
                methods.forkEvery { compute { it to it.digest() } }.pcompute()
            }
                .map { methodsAndDigests ->
                    val (methods, digests) = methodsAndDigests.unzip()
                    val digest = digests.first()
                    val differentDigest = digests.asSequence().withIndex().drop(1).find { (_, d) -> d != digest }
                    if (differentDigest != null) {
                        // if you like to debug
                        //      for (index in listOf(0, differentDigest.index)) {
                        //          vc.data.parser.serializeTAC(methods[index].toCanonical(), FileWriter(System.getProperty("user.dir") + "/method-$index"))
                        //      }
                        throw InconsistentDigestError(path, digests)
                    }
                    // prepare args for the next steps - need just the first one since all the methods are equivalent
                    val method = methods.first()
                    method to digest
                }
                .bind { (method, digest) ->
                    compute {
                        /** make sure that `digest` value is stable between cache write+read ([ObjectSerialization.writeObject], [ObjectSerialization.readObject]) **/
                        val serde = { tac: CoreTACProgram ->
                            val baos = ByteArrayOutputStream()
                            ObjectSerialization.writeObject(tac, baos)
                            ObjectSerialization.readObject<CoreTACProgram>(ByteArrayInputStream(baos.toByteArray()))
                        }
                        val deserialized = serde(method)
                        val deserializedDigest = deserialized.digest()
                        Assertions.assertEquals(digest, deserializedDigest)
                        Triple(method, digest, Randomizer(Random(0)))
                    }
                }.andAlsoInParallel(testRepetitions) { (method, digest, randomizer) ->
                    // TACMeta.CVL_DISPLAY_NAME.isCanonical = false -> so inserting different values should not matter
                    val newRandomizer = randomizer.fork()
                    val ptr = method.randCmdPointer(newRandomizer)
                    val digestA = method.pushMeta(ptr, TACMeta.CVL_DISPLAY_NAME, "blah").digest()
                    Assertions.assertNotEquals(
                        digest,
                        digestA,
                        mutationResultedInSameDigestForMethodMsg(path, digest, method, "push metadata")
                    )

                    val digestB = method.pushMeta(ptr, TACMeta.CVL_DISPLAY_NAME, "blee").digest()
                    Assertions.assertEquals(
                        digestA,
                        digestB
                    ) { "digests $digestA != $digestB after pushing non-canonical meta to $method in $ptr" }
                }.andAlsoInParallel(testRepetitions) { (method, digest, randomizer) ->
                    val modifiedField = randomizer.randomNBIdField()
                    val (mapper, old, new) = method.createNBIdMapper(modifiedField, randomizer)
                    val (newBlocks, newGraph, procedures) = method.remap(mapper, Unit)
                    val tac = method.copy(code = newBlocks, blockgraph = newGraph, procedures = procedures)
                    checkModifiedDigest(path, method, digest, tac, modifiedField, old, new)
                }.andAlsoInParallel(testRepetitions) { (method, digest, _) ->
                    val digestA = method.modifyVar().digest()
                    Assertions.assertEquals(
                        digest,
                        digestA,
                        originalAndCopyHaveDifferentDigests(path, digest, digestA)
                    )
                }.andAlsoInParallel(testRepetitions) { (method, digest, _) ->
                    val digestA = method.modifyVarToConst().digest()
                    Assertions.assertNotEquals(
                        digest,
                        digestA,
                        mutationResultedInSameDigestForMethodMsg(path, digest, method, "modifyVarToConst")
                    )
                }
                .andAlsoInParallel(testRepetitions) { (method, digest, randomizer) ->
                    val newRandomizer = randomizer.fork()
                    val digestA = method.modifySingleVar(newRandomizer).digest()
                    Assertions.assertEquals(
                        digest,
                        digestA,
                        originalAndCopyHaveDifferentDigests(path, digest, digestA)
                    )
                }.andAlsoInParallel(testRepetitions) { (method, digest, _) ->
                    val digestA = method.replaceSingleCommand().digest()
                    Assertions.assertNotEquals(
                        digest,
                        digestA,
                        mutationResultedInSameDigestForMethodMsg(path, digest, method, "replace single")
                    )
                }.andAlsoInParallel(testRepetitions) { (method, digest, randomizer) ->
                    val newRandomizer = randomizer.fork()
                    val digestA = method.replaceLastCmdInRandomBlock(newRandomizer).digest()
                    Assertions.assertNotEquals(
                        digest,
                        digestA,
                        mutationResultedInSameDigestForMethodMsg(path, digest, method, "replace last")
                    )
                }
        }.pcompute()

        ParallelPool().use { runPool -> runPool.run(theTest) }
    }

    private fun mutationResultedInSameDigestForMethodMsg(
        path: String,
        digest: String,
        method: CoreTACProgram,
        context: String = "None"
    ): String {
        return "In $path, mutation resulted in the same digests($digest) found for $method. Context: $context"
    }

    private fun originalAndCopyHaveDifferentDigests(path: String, originalDigest: String, newDigest: String): String {
        return "$path original had digest $originalDigest, but copy has digest $newDigest"
    }

    private fun checkModifiedDigest(
        path: String,
        method: CoreTACProgram,
        digest: String,
        tac: CoreTACProgram,
        modifiedField: NBIdFieldSelector,
        old: Int,
        new: Int,
    ) {
        val newDigest = tac.digest()
        if (modifiedField.modificationShouldPreserveDigest(method, old)) {
            Assertions.assertEquals(
                digest,
                newDigest
            ) { "$path mapping $modifiedField failed: original had digest $digest, but copy has digest $newDigest. Old Value $old, new value $new" }
        } else {
            Assertions.assertNotEquals(
                digest,
                newDigest
            ) { "$path mapping $modifiedField failed: original and copy have the same digest. Old $old, new $new" }
        }
    }


    open fun testArrayAnalysisWideDigests(solc: String, optimize: Boolean) = testConsistentDigest(
        solc, optimize,
        "analysis/AbiDecodeDynamicWide.sol",
        numberOfCompiles = 10
    )

    open fun testArrayAnalysisDigests(solc: String, optimize: Boolean) = testConsistentDigest(
        solc, optimize,
        "analysis/AbiDecode.sol",
        "analysis/AbiDecodeDynamic.sol",
        "analysis/AbiDecodeDynamicWide.sol",
        "analysis/TestDecodeReturnBuffer.sol",
        "analysis/StringReturn.sol",
        "analysis/ArrayArgument.sol",
        "analysis/ArrayAddressArgument.sol",
        "analysis/StringArgument.sol",
        "analysis/StringArgumentCalldata.sol",
        "analysis/EncodePacked.sol",
        "analysis/StorageStringPackedEncode.sol",
        "analysis/StructArrayArgument.sol",
        "analysis/StructWithArrayReturn.sol",
        "analysis/ConstantUintAlloc.sol",
        "analysis/ConstantStructAlloc.sol",
        "analysis/StringGetter.sol",
        "analysis/StringInMapGetter.sol",
        "analysis/OptimizedAddressReturn.sol",
    )

    open fun testConstantSizeDigests(solc: String, optimize: Boolean) = testConsistentDigest(
        solc, optimize,
        "analysis/ConstantUintAlloc.sol",
        "analysis/ConstantStructAlloc.sol",
        "analysis/StringGetter.sol",
        "analysis/StringInMapGetter.sol",
        "analysis/OptimizedAddressReturn.sol",
    )

    open fun testInlineAssemblyDigests(solc: String, optimize: Boolean) = testConsistentDigest(solc, optimize, "analysis/InlineAssembly.sol")

    open fun testABIV2EncodingDigests(solc: String, optimize: Boolean) = testConsistentDigest(
        solc, optimize,
        "analysis/StringReturn.sol",
        "analysis/ArrayArgument.sol",
        "analysis/ArrayAddressArgument.sol",
        "analysis/StringArgument.sol",
        "analysis/StringArgumentCalldata.sol",
        "analysis/EncodePacked.sol",
        "analysis/StorageStringPackedEncode.sol",
        "analysis/StructArrayArgument.sol",
        "analysis/StructWithArrayReturn.sol"
    )


    private fun getSceneWithUnrolling(path: String, solc: String): Scene =
        this.loadScene(path, solc).apply {
            this.mapContractMethodsInPlace("unrolling") { _, m ->
                m.code = BMCRunner(4, m.code as CoreTACProgram).bmcUnroll()
            }
            this.mapContractMethodsInPlace("resolve") { iScene: IScene, method: ITACMethod ->
                ExtCallSummarization.annotateCallsAndReturns(scene = iScene, method = method)
            }
        }


    open fun digestCallWithData(solc: String) {
        val path = "analysis/CalldataWithArrayScalarization.sol"
        val methodsA = getSceneWithUnrolling(path, solc).getContracts().sortedBy { it.name }
            .flatMap { contract -> contract.getMethods().sortedBy { it.name } }
        val methodsB = getSceneWithUnrolling(path, solc).getContracts().sortedBy { it.name }
            .flatMap { contract -> contract.getMethods().sortedBy { it.name } }

        for ((methodA, methodB) in methodsA.zip(methodsB)) {
            val digestA = (methodA.code as CoreTACProgram).digest()
            val digestB = (methodB.code as CoreTACProgram).digest()
            Assertions.assertEquals(digestA, digestB) { "methodA:$methodA != methodB:$methodB for $path" }
        }
    }

    open fun testDigestChangeOnReplaceDivWithSub(solc: String, optimize: Boolean) {
        val path = "analysis/Divider.sol"
        val method = loadTestContractMethod(path, solc, optimize).code as CoreTACProgram
        val digest = method.digest()
        val newTAC = method.replaceDivisionWithSubtraction()
        val newDigest = newTAC.digest()

        Assertions.assertNotEquals(digest, newDigest, mutationResultedInSameDigestForMethodMsg(path, digest, method))
    }

    open fun testDigestChangeOnBinOpReplacement(solc: String, optimize: Boolean) {
        val path = "analysis/BinOp.sol"
        val method = loadTestContractMethod(path, solc, optimize).code as CoreTACProgram
        val digest = method.digest()

        for (replacedBinExpType in TACExpr.BinOp::class.sealedSubclasses) {
            if (replacedBinExpType == TACExpr.BinOp.SignExtend::class ||
                replacedBinExpType == TACExpr.BinOp.IntSub::class ||
                replacedBinExpType == TACExpr.BinOp.IntDiv::class ||
                replacedBinExpType == TACExpr.BinOp.IntMod::class ||
                replacedBinExpType == TACExpr.BinOp.IntExponent::class ||
                replacedBinExpType == TACExpr.BinOp.BWXOr::class ||
                replacedBinExpType == TACExpr.BinOp.ShiftRightArithmetical::class
            ) {
                continue
            }
            for (newBinExpType in TACExpr.BinOp::class.sealedSubclasses) {
                val digestAfterReplace = method.replaceBinOp(replacedBinExpType) { o1, o2 ->
                    newBinExpType.primaryConstructor!!.call(o1, o2, null)
                }.digest()
                Assertions.assertNotEquals(
                    digest,
                    digestAfterReplace,
                    mutationResultedInSameDigestForMethodMsg(path, digest, method)
                )
            }
        }
    }

    private fun CoreTACProgram.replaceDivisionWithSubtraction(): CoreTACProgram {
        val (p, divExp) = analysisCache.graph.commands.mapNotNull { it.ptr `to?` (it.cmd as? TACCmd.Simple.AssigningCmd.AssignExpCmd) }
            .mapNotNull { (ptr, cmd) -> ptr to cmd `to?` (cmd.rhs as? TACExpr.BinOp.Div) }.first()
        val (cmdPointer, divCmd) = p

        val patchingProgram = toPatchingProgram()
        patchingProgram.replace(cmdPointer) { _, _ ->
            listOf(
                divCmd.copy(rhs = TACExpr.BinOp.Sub(divExp.o1, divExp.o2, divExp.tag))
            )
        }
        val (code, blockgraph) = patchingProgram.toCode()
        return this.copy(code = code, blockgraph = blockgraph)
    }

    private fun <T : TACExpr.BinOp> CoreTACProgram.replaceBinOp(
        replacedBinExpType: KClass<T>,
        ctor: (TACExpr, TACExpr) -> TACExpr.BinOp
    ): CoreTACProgram {
        val (cmdPointer, oldCmd) = analysisCache.graph.commands.mapNotNull { it.ptr `to?` (it.cmd as? TACCmd.Simple.AssigningCmd.AssignExpCmd) }
            .first { (_, cmd) -> replacedBinExpType.isInstance(cmd.rhs) }

        val oldExp = oldCmd.rhs as TACExpr.BinOp
        val cmd = oldCmd.copy(rhs = ctor(oldExp.o1, oldExp.o2))
        val patchingProgram = toPatchingProgram()
        patchingProgram.replace(cmdPointer) { _, _ ->
            listOf(
                cmd
            )
        }
        val (code, blockgraph) = patchingProgram.toCode()
        return this.copy(code = code, blockgraph = blockgraph)
    }
}

fun <V> parallel.Parallel<V>.andAlsoInParallel(numberOfIterations: Int, f: (V) -> Unit): parallel.Parallel<V> =
    bind {
        (0 until numberOfIterations).forkEvery { _ -> compute { f(it) } }.pcompute().map { _ -> it }
    }


fun CoreTACProgram.randCmdPointer(randomizer: Randomizer): CmdPointer {
    for (retries in 0 until 100) {
        val (_, blockId) = randomizer.randFromCollection(code.keys.toList())
        val cmds = code[blockId]!!
        val (index, cmd) = randomizer.randFromCollection(cmds)
        if (cmd !is TACCmd.Simple.NopCmd) {
            return CmdPointer(blockId, index)
        }
    }
    throw Exception("failed to find pos for 100 retries")
}

fun CoreTACProgram.pushMeta(key: MetaKey<String>, randomizer: Randomizer) =
    pushMeta(randCmdPointer(randomizer), key, "blah")

fun CoreTACProgram.pushMeta(ptr: CmdPointer, key: MetaKey<String>, value: String): CoreTACProgram {
    val cmds = code[ptr.block]!!.toMutableList()
    cmds[ptr.pos] = cmds[ptr.pos].mapMeta { it.plus(key to value) }
    return copy(code = code.plus(ptr.block to cmds))
}

fun CoreTACProgram.createNBIdMapper(
    fieldSelector: NBIdFieldSelector,
    randomizer: Randomizer
): Triple<CodeRemapper<Unit>, Int, Int> = run {
    val modifiedFieldValues = code.keys.map { nbId -> fieldSelector.get(nbId) }
    val (_, targetModifiedFieldValue) = randomizer.randFromCollection(modifiedFieldValues)
    val newFieldValue = generateSequence { randomizer.nextInt() }.first { it !in modifiedFieldValues }

    Triple(
        buildCodeRemapper(
            blockRemapper = { id, _, _, _ ->
                fieldSelector.maybeModifyField(id, targetModifiedFieldValue, newFieldValue)
            },
            callIndexStrategy = { _, idx, _ ->
                idx.takeIf { it != targetModifiedFieldValue || fieldSelector != NBIdFieldSelector.CALLEE_IDX }
                    ?: newFieldValue
            },
        ), targetModifiedFieldValue, newFieldValue
    )
}

fun CoreTACProgram.modifySingleVar(randomizer: Randomizer): CoreTACProgram {
    val valNamePrefixes = code.values.flatten().flatMap { it.freeVars() }.map { it.namePrefix }
    val (_, valNamePrefixToReplace) = randomizer.randFromCollection(valNamePrefixes.toList() - GLOBAL_KEYWORDS)

    val mapper = buildCodeRemapper(variableMapper = { _: Unit, v ->
        v.copy(namePrefix = "haha".takeIf { v.namePrefix == valNamePrefixToReplace }
            ?.let { v.namePrefix + it } ?: v.namePrefix)
    }).mapper(Unit)

    val ufAxioms =
        UfAxioms(ufAxioms.mapTo { it.mapValues { (_, v) -> v.map { ax -> ax.copy(exp = mapper.mapExpr(ax.exp)) } } })

    val newBlocks = code.mapValues { e -> e.value.map(mapper::map) }

    return copy(instrumentationTAC = instrumentationTAC.copy(ufAxioms = ufAxioms), code = newBlocks)
}

fun CoreTACProgram.replaceSingleCommand(): CoreTACProgram {
    val patchingProgram = toPatchingProgram()
    val blockId = code.keys.first()
    val pos = 0
    val cmdPointer = CmdPointer(blockId, pos)
    Assertions.assertNotEquals(code[blockId]!!.first(), TACCmd.Simple.NopCmd, "First command in program is NopCmd")
    patchingProgram.replace(cmdPointer) { _, _ -> listOf(TACCmd.Simple.NopCmd) }
    val (code, blockgraph) = patchingProgram.toCode()
    return this.copy(code = code, blockgraph = blockgraph)
}

fun CoreTACProgram.replaceLastCmdInRandomBlock(randomizer: Randomizer): CoreTACProgram {
    val (_, blockId) = randomizer.randFromCollection(code.keys.toList())

    // Replace the last command in the block
    val pos = code[blockId]!!.size - 1
    val cmdPointer = CmdPointer(blockId, pos)
    val randomNBIdSeq = fun() =
        generateSequence {
            randomizer.randFromCollection(code.keys.toList())
        }.map { (_, nbid) -> nbid }
    val dst = randomNBIdSeq()
        .first { it != blockId }
    val elseDst =
        randomNBIdSeq()
            .first { it != blockId && it != dst }
    val newCmd = TACCmd.Simple.JumpiCmd(
        dst, elseDst, cond = TACSymbol.Const(BigInteger.valueOf(10)),
    )

    val patchingProgram = toPatchingProgram()
    patchingProgram.replace(cmdPointer) { _, _ ->
        listOf(
            newCmd
        )
    }
    val (code, blockgraph) = patchingProgram.toCode()
    return this.copy(code = code, blockgraph = blockgraph)
}


fun CoreTACProgram.modifyVar(): CoreTACProgram {
    val mapper =
        buildCodeRemapper(variableMapper = { _: Unit, v ->
            if (v.namePrefix !in GLOBAL_KEYWORDS) {
                v.copy(namePrefix = v.namePrefix + "haha")
            } else {
                v
            }
        }).mapper(Unit)

    val ufAxioms =
        UfAxioms(ufAxioms.mapTo { it.mapValues { (_, v) -> v.map { ax -> ax.copy(exp = mapper.mapExpr(ax.exp)) } } })

    val newBlocks = code.mapValues { e -> e.value.map(mapper::map) }

    return copy(instrumentationTAC = instrumentationTAC.copy(ufAxioms = ufAxioms), code = newBlocks)
}


fun CoreTACProgram.modifyVarToConst(): CoreTACProgram {
    val mapper = buildCodeRemapper<Unit>().mapper(Unit) {
        object : QuantDefaultTACExprTransformer() {
            override fun transformFreeVar(acc: QuantVars, exp: TACExpr.Sym.Var): TACExpr =
                TACExpr.Sym.Const(
                    s = TACSymbol.Const(
                        value = BigInteger.valueOf(exp.s.callIndex.toLong()),
                        tag = exp.s.tag
                    )
                )
        }
    }

    val ufAxioms =
        UfAxioms(ufAxioms.mapTo { it.mapValues { (_, v) -> v.map { ax -> ax.copy(exp = mapper.mapExpr(ax.exp)) } } })

    val newBlocks = code.mapValues { e -> e.value.map(mapper::map) }

    return copy(instrumentationTAC = instrumentationTAC.copy(ufAxioms = ufAxioms), code = newBlocks)
}
