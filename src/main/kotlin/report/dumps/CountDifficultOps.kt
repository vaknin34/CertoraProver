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

package report.dumps

import analysis.CmdPointer
import analysis.LTACCmd
import analysis.TACBlock
import analysis.TACCommandGraph
import analysis.worklist.StepResult
import analysis.worklist.VisitingWorklistIteration
import config.Config
import datastructures.stdcollections.*
import kotlinx.serialization.Serializable
import log.*
import tac.IBlockId
import tac.NBId
import utils.*
import vc.data.*

private val logger = Logger(LoggerTypes.SPLIT)

/**
 * @param weight the weight of an item with this difficulty inside the heuristical computation -- the higher the weight,
 *    the more an occurrence of this feature raises the difficulty of the formula
 * @param shortName short name for displaying on the html pages
 *
 * Note that these will need (continual) reworking -- e.g. a nonlinear operation should probably be worth more than 3
 * Boolean decisions..
 */
enum class Difficulty(val weight: Int, val shortName: String) {
    NonLinearity(3, "nonLin"),
    ConstBaseExponentiation(2, "exponentiation"),
    CaseSplits(1, "caseSplit"),
    ;
}

/**
 * Operators that may occur in TAC programs, and that exhibit one of the [Difficulty]s.
 *
 * Note that we're not listing all the TAC operators here, but rather group them into rough
 * "difficulty equivalence classes". -- we're not distinguishing Mul and IntMul for instance, since they're just one
 * linear operation apart so to speak.
 *
 * I'm a bit unsure if we should e.g. group Div and Mod into one, since they're producing the same nonlinearity so to
 * speak keeping them apart for now, but let's consider these as a bit "in flow" for the moment ...
 */
@Serializable
sealed class DifficultOp(private val displayName: String, val difficulty: Difficulty): HasKSerializable {
    override fun toString(): String = displayName

    @Serializable
    object Mul : DifficultOp("Mul", Difficulty.NonLinearity)
    @Serializable
    object Div : DifficultOp("Div", Difficulty.NonLinearity)
    @Serializable
    object Mod : DifficultOp("Mod", Difficulty.NonLinearity)
    @Serializable
    object Ite : DifficultOp("Ite", Difficulty.CaseSplits)
    /** */
    @Serializable
    object SDiv : DifficultOp("SDiv", Difficulty.NonLinearity)
    @Serializable
    object SMod : DifficultOp("SMod", Difficulty.NonLinearity)
    /** Counting these under [Difficulty.CaseSplits] since, at least in LIA/NIA, they expand to something like
     * `x /\ y \/ a /\ b`, where the subformulas are regular comparisons.  */
    @Serializable
    object SignedComp: DifficultOp("SignedComp", Difficulty.CaseSplits)
    /** Counting simple constant-base exponentiations (expected to be 2^x or 10^x mostly). */
    @Serializable
    object ConstantBaseExponentiation: DifficultOp("ConstBaseExp", Difficulty.ConstBaseExponentiation)
}

/**
 * Analyses blocks and commands for potential difficulty (for the SMT solvers) by counting occurrences of operations
 * like Mul, Div, Ite.. (also looking at arguments to see if they're constant, but nothing deeper)
 */
class CountDifficultOps(val tacProgram: CoreTACProgram) {
    private val cache = mutableMapOf<IBlockId, BlockDifficulty?>()

    companion object {
        /**
         * Given a graph [g], a starting pointer [start], and exit points [exits],
         * computes the difficulty of the subgraph defined by [start] and [exits].
         * This method assumes that [start] and [exits] are valid pointers in [g] and
         * are indeed forming a subgraph, as we simply iterate from [start] until reaching a pointer in [exits].
         *
         * Note that the commands at the exit pointers themselves are not counted, while the one at the start pointer is
         * counted.
         */
        fun computeDifficultyInSubgraph(g: TACCommandGraph, start: CmdPointer, exits: Collection<CmdPointer>): BlockDifficulty {
            val blockDifficulty = BlockDifficulty()
            object : VisitingWorklistIteration<CmdPointer, Unit, Unit>() {
                override fun process(it: CmdPointer): StepResult<CmdPointer, Unit, Unit> {
                    val lcmd = g.elab(it)

                    processCmd(lcmd, blockDifficulty)
                    return this.cont(g.succ(it).filter { it !in exits })
                }

                override fun reduce(results: List<Unit>) {}
            }.submit(setOf(start))
            return blockDifficulty
        }

        fun processBlock(block : TACBlock, stats: BlockDifficulty = BlockDifficulty()): BlockDifficulty {
            block.commands.forEach {
                processCmd(it, stats)
            }
            return stats
        }

        fun processCmd(ltacCmd: LTACCmd, blockDifficulty: BlockDifficulty) {
            val diffOpToCount = SimpleCounterMap<DifficultOp>()
            when (val cmd = ltacCmd.cmd) {
                is TACCmd.Simple.AssigningCmd.AssignExpCmd -> processExp(cmd.rhs, diffOpToCount)
                is TACCmd.Simple.AssumeExpCmd -> processExp(cmd.cond, diffOpToCount)
                else -> Unit
            }
            blockDifficulty.update(diffOpToCount, ltacCmd.ptr)
        }

        /** Processes [e] and its sub-expressions */
        private fun processExp(e: TACExpr, cMap: SimpleCounterMap<DifficultOp>) {
            e.getOperands().forEach {
                processExp(it, cMap)
            }
            processExpFlat(e, cMap)
        }

        /**
         * Processes [e] but not its sub-expressions. That is, adds its findings in the top level [e] to [cMap].
         * It returns the non-constants operands of [e] .
         */
        fun processExpFlat(e : TACExpr, cMap : SimpleCounterMap<DifficultOp>?) : List<TACExpr> {
            fun countOp(op: DifficultOp?, count: Int = 1) {
                if (op != null && count != 0) {
                    cMap?.add(op, count)
                }
            }

            return when (e) {
                is TACExpr.Vec.Mul,
                is TACExpr.Vec.IntMul -> {
                    val nonConsts = e.getOperands().filter { it !is TACExpr.Sym.Const }
                    runIf(nonConsts.size > 1) {
                        countOp(DifficultOp.Mul, nonConsts.size - 1)
                        nonConsts
                    }
                }

                is TACExpr.BinOp -> when (e) { // need this extra level so o1, o2 are available also when grouping cases
                    is TACExpr.BinOp.Div,
                    is TACExpr.BinOp.IntDiv,
                    is TACExpr.BinOp.SDiv,
                    is TACExpr.BinOp.Mod,
                    is TACExpr.BinOp.SMod ->
                        runIf (e.o2 !is TACExpr.Sym.Const) {
                            when (e) {
                                is TACExpr.BinOp.Div, is TACExpr.BinOp.IntDiv -> DifficultOp.Div
                                is TACExpr.BinOp.SDiv -> DifficultOp.SDiv
                                is TACExpr.BinOp.Mod -> DifficultOp.Mod
                                is TACExpr.BinOp.SMod -> DifficultOp.SMod
                                else -> `impossible!`
                            }.let(::countOp)
                            listOf(e.o2)
                    }
                    is TACExpr.BinOp.Exponent,
                    is TACExpr.BinOp.IntExponent -> {
                        val o2 = e.o2 // for the smart cast ..
                        if (o2 !is TACExpr.Sym.Const) {
                            if (e.o1 is TACExpr.Sym.Const) {
                                DifficultOp.ConstantBaseExponentiation
                            } else {
                                // variable base and exponent exponentiation, currently we don't add any axioms
                                // for this -- it's simple for the solvers but very imprecise
                                null
                            }.let(::countOp)
                        } else {
                            // e.o2 is constant
                            // we assume that e.o1 is non-constant here, since if both were constant, we'd just have computed the value
                            // our axiomatization flattens this into multiplications -- so we count those
                            (o2.s.value.toIntOrNull())?.let {
                                countOp(DifficultOp.Mul, it - 1)  // x^n expands to n-1 multiplications
                            }
                        }
                        e.getOperands().filter { it !is TACExpr.Sym.Const }
                    }
                    is TACExpr.BinOp.ShiftLeft ->
                        runIf(e.o2 !is TACExpr.Sym.Const) {
                            countOp(DifficultOp.ConstantBaseExponentiation)
                            if (e.o1 !is TACExpr.Sym.Const) {
                                countOp(DifficultOp.Mul)
                                listOf(e.o1, e.o2)
                            } else {
                                listOf(e.o2)
                            }
                        }

                    is TACExpr.BinOp.ShiftRightLogical,
                    is TACExpr.BinOp.ShiftRightArithmetical ->
                        runIf(e.o2 !is TACExpr.Sym.Const) {
                            countOp(DifficultOp.ConstantBaseExponentiation)
                            if (e.o1 !is TACExpr.Sym.Const) {
                                countOp(DifficultOp.Div)
                                listOf(e.o1, e.o2)
                            } else {
                                listOf(e.o2)
                            }
                        }

                    else -> null
                }

                is TACExpr.BinRel.Sge,
                is TACExpr.BinRel.Sle,
                is TACExpr.BinRel.Sgt,
                is TACExpr.BinRel.Slt -> {
                    countOp(DifficultOp.SignedComp)
                    null
                }

                is TACExpr.TernaryExp.MulMod -> {
                    val res = mutableListOf<TACExpr>()
                    // count this like a mul and a mod
                    if (e.o1 !is TACExpr.Sym.Const && e.o2 !is TACExpr.Sym.Const) {
                        countOp(DifficultOp.Mul)
                        res += e.o1
                        res += e.o2
                    }
                    if (e.o3 !is TACExpr.Sym.Const) {
                        countOp(DifficultOp.Mod)
                        res += e.o3
                    }
                    return res
                }

                is TACExpr.TernaryExp.Ite -> {
                    countOp(DifficultOp.Ite)
                    null
                }

                else -> null
            }.orEmpty()
        }

    }

    fun getDifficultCmds() = tacProgram.blockgraph.keys
        .flatMapToSet { block ->
            (get(block)?.heuristicallyDifficultCmds.orEmpty()).asIterable()
        }

    fun getDifficultBlocks() = tacProgram.blockgraph.keys.filter { block -> get(block)?.isDifficult() == true }

    operator fun get(block: IBlockId): BlockDifficulty? =
        cache.computeIfAbsent(block) {
            run(block)
        }

    private fun run(blockId: IBlockId): BlockDifficulty? {
        // this cast won't fail as long as all implementers of [IBlockId] are subclasses of NBId, which is the case
        // now ..
        val nbId = (blockId as? NBId) ?: run {
            logger.warn {
                "found an IBlockId ($blockId) that is not an NBId -- this is new .. " +
                    "block ad-hoc difficulty analysis failed"
            }
            return null
        }

        return BlockDifficulty().also { blockDifficulty ->
            tacProgram.analysisCache.graph.elab(nbId).commands.forEach { cmd -> processCmd(cmd, blockDifficulty) }
        }
    }
}


/** The result of [CountDifficultOps] for a block ([NBId]) */
class BlockDifficulty {
    private val difficultOpData: MutableMap<DifficultOp, DiffOpData> = mutableMapOf()

    fun getOccurrenceCount(opPred: (DifficultOp) -> Boolean): Int =
        difficultOpData.entries.fold(0) { acc, (op, data) -> acc + if (opPred(op)) { data.number } else { 0 } }

    fun getOccurrenceCount(op: DifficultOp) =
        getOccurrenceCount { it == op }

    val heuristicallyDifficultCmds
        get() =
            difficultOpData.values.fold(sequenceOf<CmdPointer>()) { acc, diffCmd -> acc + diffCmd.occurrences.asSequence() }

    fun computeDifficultyScore() =
        difficultOpData.entries.sumOf { (type, data) -> (data.number * type.difficulty.weight) }

    /** The heuristic saying whether we mark a block as "might be difficult", based on the fields of this class. */
    fun isDifficult(): Boolean =
        computeDifficultyScore() >= Config.Smt.BlockIsDifficultThreshold.get()

    val asText: String
        get() =
            difficultOpData.entries.groupBy { (type, _) -> (type.difficulty to type) }.entries.map { (difficultyToOpType, typeCmdInfoPairs) ->
                val (difficulty, opType) = difficultyToOpType
                "#${difficulty.shortName}${opType}: ${typeCmdInfoPairs.fold(0) { acc, p -> acc + p.value.number}}"
            }.joinToString("\n")

    fun update(analysisData: SimpleCounterMap<DifficultOp>, cmd: CmdPointer) {
        analysisData.entries.forEach { (diffOp, count) ->
            difficultOpData.updateInPlace(diffOp, default = DiffOpData()) {
                if (count > 0) {
                    it.number += count
                    it.occurrences += cmd
                }
                it
            }
        }
    }

    /**
     * The data we collect for one given [DifficultOp].
     * Includes the commands that have it [occurrences] and the overall number of occurrences [number]
     * A command might have more than one operation of the same type -- thus [number] does not equal [occurrences.size]
     */
    private class DiffOpData(val occurrences: MutableSet<CmdPointer> = mutableSetOf(), var number: Int = 0)
}
