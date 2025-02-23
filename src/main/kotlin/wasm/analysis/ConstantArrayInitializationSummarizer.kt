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

@file:kotlinx.serialization.UseSerializers(BigIntegerSerializer::class)
package wasm.analysis

import analysis.*
import datastructures.stdcollections.*
import analysis.loop.AbstractArraySummaryExtractor
import analysis.loop.ArrayLoopSummarization
import analysis.loop.LoopSummarization
import analysis.smtblaster.IBlaster
import analysis.smtblaster.Z3BlasterPool
import com.certora.collect.*
import log.*
import parallel.Parallel
import parallel.ParallelPool
import parallel.Scheduler.complete
import parallel.forkEvery
import parallel.pcompute
import tac.MetaMap
import tac.NBId
import utils.*
import vc.data.*
import vc.data.tacexprutil.*
import java.math.BigInteger

private val logger = Logger(LoggerTypes.WASM)

/**
 * Identify loops like
 *
 * HEAD:
 *   B = I < K
 *   JUMP B LOOP DONE
 *
 * LOOP:
 *   P = A + I
 *   M[P] = C
 *   TMP = I + Stride
 *   I = TMP
 *   JUMP HEAD
 *
 * DONE:
 *   ...
 *
 * s.t. we write C to evey address in the range [A, A+Stride, A+2*Stride, ... A+(L-1)*Stride]
 *
 * We refer to this (the entire closed interval from [A,A+(L-1)*Stride] as an Array
 */
object ConstantArrayInitializationSummarizer {

    /**
     * [ConstArrayInitLengthHeuristic]s know how to guess the (constant) number of iterations
     * a loop will execute, and the Stride of the loop.
     *
     * In the example in the docs for [ConstantArrayInitializationSummarizer], the stride would be
     * "Stride". The number of iterations would be
     * some N s.t. Stride*N == K, if it exists and can be determined.
     */
    interface ConstArrayInitLengthHeuristic {
        fun guessElemSizeAndLength(
            g: TACCommandGraph,
            loopSummary: LoopSummarization.LoopIterationSummary,
            interpolation: Map<TACSymbol.Var, AbstractArraySummaryExtractor.Interpolation>
        ): Pair<List<BigInteger>, BigInteger?>

        fun guessOffset(
            g: TACCommandGraph,
            loopSummary: LoopSummarization.LoopIterationSummary,
            interpolation: Map<TACSymbol.Var, AbstractArraySummaryExtractor.Interpolation>
        ): BigInteger?
    }

    /**
     * Guess the elem size/length from syntactic conditions:
     * - If we have a variable that is incremented by a fixed amount on each iteration,
     *   use that amount as the size S
     * - If we have a literal N that appears in the loop condition,
     *   and S divides L, use L/S as the number of iterations
     */
    object SyntacticConditionLengthHeuristic: ConstArrayInitLengthHeuristic {
        override fun guessElemSizeAndLength(
            g: TACCommandGraph,
            loopSummary: LoopSummarization.LoopIterationSummary,
            interpolation: Map<TACSymbol.Var, AbstractArraySummaryExtractor.Interpolation>
        ): Pair<List<BigInteger>, BigInteger?> {
            // We're interested in constant increments as described above,
            // so find all variables that have a Linear interpolation
            // (i.e. their value at iteration I is I*(the linear incr amount) + the initial value)
            val linearEffects = interpolation
                .values
                .mapNotNull {
                    it.tryAs<AbstractArraySummaryExtractor.Interpolation.Linear>()?.n
                }

            // Grab all the constants that appear in the exit condition, as one of these could be
            // the length
            val lenCandidates = loopSummary
                .exitCondition
                .subs
                .toConstSet()
                .mapNotNullToSet { it.value.takeIf { it != BigInteger.ZERO } }

            // Find a unique S, L s.t. S \in linearEffects, N \in lenCandidates, and S divides N.
            // If these exist, S is our size/stride, and L/S is our number of iterations/logical length.
            val lenCandidatesWithSize = lenCandidates.mapNotNull { lenCandidate ->
                linearEffects.mapNotNull { incrCandidate ->
                    val (len, rem) = lenCandidate.divideAndRemainder(incrCandidate)
                    (listOf(incrCandidate) to len).takeIf { rem == BigInteger.ZERO }
                }.uniqueOrNull()
            }

            return lenCandidatesWithSize.maxByOrNull { (_, l) -> l } ?: linearEffects to null
        }

        private fun TACExpr.constOrZero(): BigInteger = evalAsConst() ?: BigInteger.ZERO

        override fun guessOffset(
            g: TACCommandGraph,
            loopSummary: LoopSummarization.LoopIterationSummary,
            interpolation: Map<TACSymbol.Var, AbstractArraySummaryExtractor.Interpolation>
        ): BigInteger? {
            // We're interested in very simple loops with a single write
            val write = loopSummary.reachingWrites[LoopSummarization.WriteTarget(TACKeyword.MEMORY.toVar(), incarn = 1)]?.singleOrNull()
            if (write == null) {
                return null
            }
            if (write !is LoopSummarization.MemoryMutation.MemoryWrite) {
                return null
            }

            return write.index.subs.fold(BigInteger.ZERO) { v, e -> v + e.constOrZero() }
        }
    }

    /**
     * Insert [ConstArrayInitSummary]s for the loops described in the description of
     * [ConstantArrayInitializationSummarizer]
     *
     * Following the example in the documentation for [ConstantArrayInitializationSummarizer], we would add a summary:
     *
     * SUMMARY:
     *   ConstantArrayInitSummary(
     *     iterations=[[K/Stride]],
     *     stride=Stride,
     *     startPtr=A,
     *     zeroVar=I,
     *     v=C,
     *     modifiedVars={I},
     *     summarizedBlocks={HEAD,LOOP},
     *     originalBlockStart=HEAD,
     *     skipTarget=DONE,
     *   )
     *
     *  s.t. SUMMARY's predecessors are HEAD and DONE
     *
     * @param lengthHeuristic is a heuristic for determining L and S as mentioned in the
     *        module description, i.e. the length and stride of such a loop.
     */
    fun annotateLoops(
        core: CoreTACProgram,
        lengthHeuristic: ConstArrayInitLengthHeuristic = SyntacticConditionLengthHeuristic
    ): CoreTACProgram {
        val g = core.analysisCache.graph
        val loops = getNaturalLoops(g)
        val analysis = ParallelPool.allocInScope(2000, { timeout -> Z3BlasterPool(z3TimeoutMs = timeout) }) { blaster ->
            val summarizer = LoopSummarization(g, blaster, loops)
            ConstantArrayInitLoopAnalysis(
                g,
                lengthHeuristic,
                loops,
                summarizer,
                blaster,
            )
        }
        val patching = core.toPatchingProgram()
        for (l in loops) {
            val summary = analysis.loopSummary(l) ?: continue
            val summaryBlock = patching.addBlock(l.head, listOf(
                TACCmd.Simple.SummaryCmd(summary, MetaMap())
            ))
            for (pred in g.pred(l.head)) {
                if (pred in l.body) {
                    continue
                }

                val lastCmd = g.elab(pred).commands.last()
                if (lastCmd.cmd is TACCmd.Simple.JumpCmd) {
                    patching.replaceCommand(lastCmd.ptr, listOf(
                        lastCmd.cmd.withDst(summaryBlock)
                    ))
                } else {
                    patching.replaceCommand(lastCmd.ptr,
                        listOf(lastCmd.cmd), treapSetOf(summaryBlock)
                    )
                }
            }
        }
        return patching.toCode(core)
    }

    class ConstantArrayInitLoopAnalysis(
        private val g: TACCommandGraph,
        private val lengthHeuristic: ConstArrayInitLengthHeuristic,
        loops: Set<Loop>,
        private val summarizer: LoopSummarization,
        private val blaster: IBlaster,
    ) {
        val annotated: Map<NBId, ConstArrayInitSummary>

        fun loopSummary(l: Loop) = annotated[l.head]

        init {
            val annotations = ParallelPool.runInherit(
                loops.forkEvery(::processLoop).pcompute(),
                ParallelPool.SpawnPolicy.GLOBAL
            )
            annotated = annotations.filterNotNull().associateBy { it.originalBlockStart }
        }

        private fun processLoop(l: Loop): Parallel<ConstArrayInitSummary?> {
            val loopSummary = summarizer.summarizeLoop(l) ?: run {
                logger.debug { "failed to summarize $l"}
                return complete(null)
            }
            // The interpolation of the summary is just
            // a mapping from each loop variable to a summary of how it is modified on each iteration.
            // This could be Identity (no change), Linear (a constant increment each iteration),
            // some Monotone transformation, etc
            val interpolation = AbstractArraySummaryExtractor.interpolateLoop(loopSummary)

            if (interpolation == null) {
                logger.debug { "failed to interpolate $loopSummary"}
                return complete(null)
            }

            val constOffset = lengthHeuristic.guessOffset(g, loopSummary, interpolation)
            val (guessSize, guessLen) = lengthHeuristic.guessElemSizeAndLength(g, loopSummary, interpolation)

            if (guessLen == null) {
                logger.debug { "did not guess a length for $loopSummary with $interpolation"}
                return complete(null)
            }

            val arrayAnalyzer = object : ArrayLoopSummarization(blaster) {
                override val elementSizes = guessSize
                override fun isConstantSizeArray(): BigInteger = guessLen
                override fun elementStartOffset(): BigInteger = constOffset ?: BigInteger.ZERO
                override fun plausibleAssignment(l: Loop, v: TACSymbol.Var, r: LoopRole): Boolean {
                    return constOffset != BigInteger.ZERO || r != LoopRole.OBJ_POINTER
                }
            }

            val summaryJob = arrayAnalyzer
                .isArrayWriteStride(loopSummary)
                .map {
                    // An element of this list effectively says that the loop
                    // writes every address with some stride in some range.
                    // The "roles" of each variable determine what this range is
                    it.uniqueOrNull()?.let {writeEvery ->
                        plausibleSummary(guessLen, constOffset ?: BigInteger.ZERO, loopSummary, interpolation, writeEvery)
                    }
                }

            return summaryJob
        }

        private fun plausibleSummary(
            length: BigInteger,
            constOffset: BigInteger,
            loopSummary: LoopSummarization.LoopIterationSummary,
            interpolation: Map<TACSymbol.Var, AbstractArraySummaryExtractor.Interpolation>,
            writeEvery: ArrayLoopSummarization.WriteEvery
        ): ConstArrayInitSummary? {
            val l = loopSummary.loop

            // A variable with the START role contains the initial address of the array/memory region
            val arrayPointer = writeEvery.roles.entries.singleOrNull() {(_, role) ->
                role == AbstractArraySummaryExtractor.LoopRole.ELEM_START
            }?.key ?: writeEvery.roles.entries.singleOrNull() { (_, role) ->
                role == AbstractArraySummaryExtractor.LoopRole.OBJ_POINTER
            }?.key ?: run {
                logger.debug { "did not find an array pointer in $writeEvery.roles"}
                return null
            }

            val constOffsetForSummary = constOffset.takeIf {
                writeEvery.roles[arrayPointer] == AbstractArraySummaryExtractor.LoopRole.OBJ_POINTER
            } ?: BigInteger.ZERO

            //O A variable with the ZERO role is assumed to be 0 initially (this is typically
            // the case for variables used as an offset from START of the array)
            val offsetVar = writeEvery.roles.entries.singleOrNull() { (_, role) ->
                role == AbstractArraySummaryExtractor.LoopRole.ZERO
            }?.key

            val modifiedVars = loopSummary
                .iterationEffect
                .keys
                .filterToSet {
                    interpolation[it] !is AbstractArraySummaryExtractor.Interpolation.Identity
                }

            val uniqueSuccessor = g.succ(l.head).singleOrNull {
                it !in l.body
            } ?: run {
                logger.debug { "loop $l does not have a unique successor"}
                return null
            }

            return ConstArrayInitSummary(
                iterations = length,
                stride = writeEvery.assumedSize,
                startPtr = arrayPointer,
                modifiedVars = modifiedVars,
                originalBlockStart = l.head,
                summarizedBlocks = l.body,
                skipTarget = uniqueSuccessor,
                elementIndex = offsetVar,
                constantOffset = constOffsetForSummary,
                v = writeEvery.write.value,
            )
        }
    }
}

/**
 * Summarizes a loop that appears to write to a statically known
 * set of addresses (e.g. to a contiguous set of array elements)
 *
 * @property iterations the number of iterations
 * @property stride the stride of the loop, i.e. difference between successive writes
 * @property startPtr the address of the first write
 * @property elementIndex the variable offset used in the loop
 * @property constantOffset a constant offset added to [startPtr], i.e.
 *           each iteration accesses [startPtr] + [constantOffset] + [elementIndex]
 * @property v denotes the syntax of the value written on each iteration
 */
@KSerializable
data class ConstArrayInitSummary(
    val iterations: BigInteger,
    val stride: BigInteger,
    val startPtr: TACSymbol,
    val elementIndex: TACSymbol.Var?,
    val constantOffset: BigInteger,
    val v: TACExpr,
    override val modifiedVars: Set<TACSymbol.Var>,
    override val summarizedBlocks: Set<NBId>,
    override val originalBlockStart: NBId,
    override val skipTarget: NBId,
): ConditionalBlockSummary {

    /**
     * @return true if
     *   - the loop-modified variables are not live after the loop,
     *   - the value _written_ on each iteration is loop-invariant
     *   - [elementIndex] must be 0 on loop entry (if not null): the condition [elementIndex] == 0 was
     *     assumed to be true when the summary was produced, and must actually be true for the
     *     summary to be valid
     *
     * These together imply the summarized loop can be replaced with a bytelongcopy
     */
    fun isValidSimpleInitialization(g: TACCommandGraph): Boolean {
        if (modifiedVars.containsAny(g.cache.lva.liveVariablesBefore(skipTarget))) {
            return false
        }

        if (modifiedVars.containsAny(v.getFreeVars())) {
            return false
        }

        val mbc = MustBeConstantAnalysis(g)
        val nonLoopPreds = g
            .pred(CmdPointer(originalBlockStart, 0))
            .filter { it.block !in summarizedBlocks }

        if (elementIndex != null && nonLoopPreds.any { mbc.mustBeConstantAt(it, elementIndex) != BigInteger.ZERO }) {
            return false
        }

        return true
    }

    override val variables: Set<TACSymbol.Var>
        get() = modifiedVars + setOfNotNull(elementIndex)

    override val annotationDesc: String
        get() = "Constant Array Initialization at $originalBlockStart, " +
            "initializing every $stride from $startPtr for $iterations elements"

    override fun remapBlocks(f: (NBId) -> NBId?): ConditionalBlockSummary {
        return this.copy(
            summarizedBlocks = summarizedBlocks.mapToSet { f(it) ?: it },
            originalBlockStart = f(originalBlockStart) ?: originalBlockStart,
            skipTarget = f(skipTarget) ?: skipTarget,
        )
    }

    override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): TACSummary {
        return this.copy(
            startPtr = startPtr.tryAs<TACSymbol.Var>()?.let(f) ?: startPtr,
            modifiedVars = modifiedVars.mapToSet(f),
        )
    }
}
