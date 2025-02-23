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

package vc.summary

import algorithms.AssociativityRequirement
import datastructures.Bijection
import vc.data.*
import vc.data.tacexprutil.TACCmdStructFlattener
import vc.data.tacexprutil.TACExprFreeVarsCollector
import vc.summary.ComputeTACSummary.*

/**
 * @param inputAlreadyInSsa if this is true, no renaming is done during summarization; we keep the identifiers as they
 *     are, all invars/outvar mappings are the identity mapping in this case
 */
class ComputeTACSummaryTransFormula(val inputAlreadyInSsa: Boolean = false) :
    ComputeTACSummary<ComputeTACSummaryTransFormula.TACSummaryTransFormula> {

    override val associativityRequirement = AssociativityRequirement.DONT_FORCE

    companion object {
        /** does all normalizations that we want to apply to all [TACCmd.Simple] before putting them into a
         * [TACTransFormula] */
        fun normalizeCmd(cmd: TACCmd.Simple): TACCmd.Simple {
            return TACCmdStructFlattener().map(cmd)
        }
    }

    override fun sequentialComposition(rs: List<TACSummaryTransFormula>): TACSummaryTransFormula.LazySeqCompSummary {
        return TACSummaryTransFormula.LazySeqCompSummary(rs, inputAlreadyInSsa)
    }

    override fun parallelComposition(rs: List<TACSummaryTransFormula>): TACSummaryTransFormula {
        // alternatively we could adapt this method, but this is easier now
        require(!inputAlreadyInSsa) { "don't use this method if input is already in SSA" }
        return TACSummaryTransFormula.LazyParCompSummary(rs)
    }

    /**
     * note: [cmdNormalized] is used for computing the contents of the [TACTransFormula], [cmd] is used as a
     * backpointer to what the summary summarizes.
     */
    override fun summarizeCmd(cmd: HasTACCommand): TACSummaryTransFormula =
        when (val cmdNormalized = normalizeCmd(cmd.cmd)) {
            is TACCmd.Simple.LabelCmd -> TACSummaryTransFormula.buildNop(cmd)
            is TACCmd.Simple.AssigningCmd -> summarizeAssign(cmdNormalized, cmd)
            is TACCmd.Simple.WordStore -> buildAssignSummary(
                cmdNormalized.base,
                TACExprFactUntyped.Store(
                    cmdNormalized.base.asSym(),
                    cmdNormalized.loc.asSym(),
                    v = cmdNormalized.value.asSym()
                ),
                cmd
            )
            is TACCmd.Simple.ByteLongCopy -> buildAssignSummary(
                cmdNormalized.dstBase,
                TACExprFactUntyped.LongStore(
                    cmdNormalized.dstBase.asSym(),
                    cmdNormalized.dstOffset.asSym(),
                    cmdNormalized.srcBase.asSym(),
                    cmdNormalized.srcOffset.asSym(),
                    cmdNormalized.length.asSym()
                ),
                cmd
            )
            is TACCmd.Simple.JumpCmd -> TACSummaryTransFormula.buildNop(cmd)
            is TACCmd.Simple.JumpiCmd -> TACSummaryTransFormula.buildNop(cmd)
            is TACCmd.Simple.JumpdestCmd -> TACSummaryTransFormula.buildNop(cmd)
            is TACCmd.Simple.LogCmd -> TACSummaryTransFormula.buildNop(cmd)

            is TACCmd.Simple.CallCore ->
                error("instances of TACCmd.Simple.CallCore should have been resolved before this point")
            is TACCmd.Simple.ReturnSymCmd,
            is TACCmd.Simple.ReturnCmd -> TACSummaryTransFormula.SimpleTACSummaryTransFormula(
                TACTransFormula.True,
                TACSummaryTag.TACCmdTag(cmd)
            )
            is TACCmd.Simple.RevertCmd -> TACSummaryTransFormula.buildNop(cmd)
            is TACCmd.Simple.AssumeCmd -> summarizeAssumeCmd(cmdNormalized.cond, false, cmd)
            is TACCmd.Simple.AssumeNotCmd -> summarizeAssumeCmd(cmdNormalized.cond, true, cmd)
            is TACCmd.Simple.AssumeExpCmd -> summarizeAssumeExpCmd(cmdNormalized.cond, cmd)
            is TACCmd.Simple.AssertCmd -> TACSummaryTransFormula.AssertSummary(
                transFormula = TACTransFormula.True,
                polarity = false,
                constraint = cmdNormalized.o,
                tag = TACSummaryTag.TACCmdTag(cmd)
            )
            is TACCmd.Simple.AnnotationCmd,
            is TACCmd.Simple.NopCmd -> TACSummaryTransFormula.buildNop(cmd)
            is TACCmd.Simple.SummaryCmd -> {
                when (cmdNormalized.summ) {
                    is ReturnSummary -> TACSummaryTransFormula.buildNop(cmd)
                    // we completely ignore Opcode summaries, as they may pop up here
                    // due to StoragePackedLengthSummarizer
                    is OpcodeSummary -> TACSummaryTransFormula.buildNop(cmd)
                    else -> throw UnsupportedOperationException(
                        "transformula summaries for this summary command " +
                                "not yet supported: ${cmdNormalized.summ}"
                    )
                }
            }
        }

    /**
     * @param polarity "true" means "negate the condition", otherwise leave it as is
     */
    private fun summarizeAssumeCmd(
        cond: TACSymbol,
        polarity: Boolean,
        hasTacCommand: HasTACCommand
    ): TACSummaryTransFormula {
        val inOutVars =
            if (cond is TACSymbol.Var)
                Bijection.fromMap(mapOf(Pair(TACSummaryVar(cond), cond.asSym())))
            else
                Bijection()
        return TACSummaryTransFormula.SimpleTACSummaryTransFormula(
            TACTransFormula(
                if (polarity) TACExprFactUntyped.LNot(cond.asSym()) else cond.asSym(),
                inOutVars, inOutVars, setOf(), setOf()
            ), hasTacCommand
        )
    }

    private fun summarizeAssumeExpCmd(cond: TACExpr, hasTACCmd: HasTACCommand): TACSummaryTransFormula {
        val freeVars = TACExprFreeVarsCollector.getFreeVars(cond)
        val inOutVars = Bijection.fromMap(freeVars.associate { fv -> Pair(TACSummaryVar(fv), fv.asSym()) })
        return TACSummaryTransFormula.SimpleTACSummaryTransFormula(
            TACTransFormula(cond, inOutVars, inOutVars, setOf(), setOf()), hasTACCmd
        )
    }


    private fun buildAssignSummary(lhs: TACSymbol.Var, rhs: TACExpr, hasTACCmd: HasTACCommand): TACSummaryTransFormula {
        val rhsVars: Set<TACSymbol> = TACExprFreeVarsCollector.getFreeVars(rhs)

        val renamedLhs =
            if (inputAlreadyInSsa) {
                lhs
            } else {
                /* we need to rename the lhs because it may also appear on the right hand side */
                TACSymbol.Factory.getFreshAuxVar(
                    TACSymbol.Factory.AuxVarPurpose.LHS,
                    lhs
                )
            }
        val inVars = Bijection.fromMap(rhsVars.map { v ->
            Pair(TACSummaryVar(v as TACSymbol.Var), v.asSym())
        }.toMap())
        val lhsTACSummaryVar = TACSummaryVar(lhs)
        val inVarsThatAreOutVars = inVars.filter { it.key != lhsTACSummaryVar }
        val outVars = Bijection.fromMap(inVarsThatAreOutVars + mapOf(Pair(lhsTACSummaryVar, renamedLhs.asSym())))
        val transFormula = TACTransFormula(
            TACExprFactUntyped.Eq(renamedLhs.asSym(), rhs),
            inVars,
            outVars,
            setOf(lhsTACSummaryVar),
            setOf()
        )
        return TACSummaryTransFormula.AssignmentSummary(
            transFormula,
            renamedLhs.asSym(),
            rhs,
            TACSummaryTag.TACCmdTag(hasTACCmd)
        )
    }

    private fun summarizeAssign(
        cmdNormalized: TACCmd.Simple.AssigningCmd,
        hasTACCmd: HasTACCommand
    ): TACSummaryTransFormula {
        return when (cmdNormalized) {
            is TACCmd.Simple.AssigningCmd.AssignExpCmd -> buildAssignSummary(
                cmdNormalized.lhs,
                cmdNormalized.rhs,
                hasTACCmd
            )
            is TACCmd.Simple.AssigningCmd.ByteLoad -> buildAssignSummary(
                cmdNormalized.lhs,
                TACExprFactUntyped.Select(cmdNormalized.base.asSym(), cmdNormalized.loc.asSym()),
                hasTACCmd
            )
            is TACCmd.Simple.AssigningCmd.ByteStore -> buildAssignSummary(
                cmdNormalized.lhs,
                TACExprFactUntyped.Store(
                    cmdNormalized.base.asSym(),
                    cmdNormalized.loc.asSym(),
                    v = cmdNormalized.value.asSym()
                ),
                hasTACCmd
            )
            is TACCmd.Simple.AssigningCmd.ByteStoreSingle -> buildAssignSummary(
                cmdNormalized.lhs,
                TACExprFactUntyped.Store(
                    cmdNormalized.base.asSym(),
                    cmdNormalized.loc.asSym(),
                    v = cmdNormalized.value.asSym()
                ),
                hasTACCmd
            )
            is TACCmd.Simple.AssigningCmd.WordLoad -> buildAssignSummary(
                cmdNormalized.lhs,
                TACExprFactUntyped.Select(cmdNormalized.base.asSym(), cmdNormalized.loc.asSym()),
                hasTACCmd
            )
            is TACCmd.Simple.AssigningCmd.AssignSimpleSha3Cmd -> buildAssignSummary(
                cmdNormalized.lhs,
                TACExprFactUntyped.SimpleHash((cmdNormalized.args.size * 32).asTACExpr, cmdNormalized.args.map { it.asSym() }),
                hasTACCmd
            )
            is TACCmd.Simple.AssigningCmd.AssignSha3Cmd -> {
                throw UnsupportedOperationException(
                    "transformula summarization not yet implemented for command " +
                            "$cmdNormalized "
                )
            }
            is TACCmd.Simple.AssigningCmd.AssignGasCmd -> {
                buildHavocSummary(cmdNormalized, hasTACCmd)
            }
            is TACCmd.Simple.AssigningCmd.AssignMsizeCmd -> {
                throw UnsupportedOperationException(
                    "transformula summarization not yet implemented for command " +
                            "$cmdNormalized "
                )
            }
            is TACCmd.Simple.AssigningCmd.AssignHavocCmd -> buildHavocSummary(cmdNormalized, hasTACCmd)
        }
    }

    /**
     * A havoc is modelled as an empty constraint (true) and an outVar but no invar. This means that subsequent
     * constraints using the havocced variable will connect to the outVar of the havoc transition, which (the outvar)
     * is disconnected from previous SSA-instances of the program var, since it is not an invar of this statement.
     */
    private fun buildHavocSummary(
        cmd: TACCmd.Simple.AssigningCmd,
        hasTACCmd: HasTACCommand
    ): TACSummaryTransFormula {
        val lhsTACSummaryVar = TACSummaryVar(cmd.lhs)
        return TACSummaryTransFormula.SimpleTACSummaryTransFormula(
            TACTransFormula(
                TACSymbol.True.asSym(),
                Bijection(),
                Bijection.fromMap(
                    mapOf(
                        Pair(
                            lhsTACSummaryVar,
                            cmd.lhs.asSym()
                        )
                    )
                ),
                setOf(lhsTACSummaryVar),
                setOf()
            ),
            hasTACCmd
        )
    }

    sealed class TACSummaryTransFormula(
        override val isNop: Boolean = false,
        override val isUnreachable: Boolean = false
    ) : TACSummaryWithTransFormula, ToLExpTransformula {

        data class NopSummary(override val tag: TACSummaryTag) :
            TACSummaryTransFormula(isNop = true, isUnreachable = false) {
            override val transFormula = TACTransFormula.True
            override fun toString(): String = "Nop"
        }

        @Suppress("DataClassShouldBeImmutable")
        data class LazySeqCompSummary(val sums: List<TACSummaryTransFormula>, val inputAlreadyInSsa: Boolean) :
            TACSummaryTransFormula() {

            private lateinit var lazyTf: TACTransFormula
            private lateinit var lazyTag: TACSummaryTag
            private var computedLazyFields = false
            private lateinit var lazySeqCompResult: SeqCompResult<TACExpr, TACSummaryVar, TACExpr.Sym.Var, TACTransFormula>

            private fun computeLazyFields() {
                if (!computedLazyFields) {
                    lazySeqCompResult =
                        TACTransFormula.sequentialComposition(sums.map { it.transFormula }, inputAlreadyInSsa)
                    lazyTf = lazySeqCompResult.tf
                    lazyTag = TACSummaryTag.sequentialComposition(sums.map { it.tag })
                    computedLazyFields = true
                }
            }

            override val tag: TACSummaryTag
                get() {
                    computeLazyFields(); return lazyTag
                }
            override val transFormula: TACTransFormula
                get() {
                    computeLazyFields(); return lazyTf
                }
            val seqCompResult: SeqCompResult<TACExpr, TACSummaryVar, TACExpr.Sym.Var, TACTransFormula>
                get() {
                    computeLazyFields(); return lazySeqCompResult
                }
        }

        @Suppress("DataClassShouldBeImmutable")
        data class LazyParCompSummary(val sums: List<TACSummaryTransFormula>) : TACSummaryTransFormula() {

            private lateinit var lazyTf: TACTransFormula
            private lateinit var lazyTag: TACSummaryTag
            private var computedLazyFields = false

            private fun computeLazyFields() {
                if (!computedLazyFields) {
                    val tf =
                        TACTransFormula.parallelComposition(sums.map { it.transFormula })
                    lazyTf = tf
                    lazyTag = TACSummaryTag.parallelComposition(sums.map { it.tag })
                    computedLazyFields = true
                }
            }

            override val tag: TACSummaryTag
                get() {
                    computeLazyFields(); return lazyTag
                }
            override val transFormula: TACTransFormula
                get() {
                    computeLazyFields(); return lazyTf
                }
        }


        data class SimpleTACSummaryTransFormula(
            override val transFormula: TACTransFormula,
            override val tag: TACSummaryTag,
            override val isNop: Boolean = false,
            override val isUnreachable: Boolean = false
        ) : TACSummaryTransFormula(isNop = true, isUnreachable = false) {
            override fun toString(): String = tag.toString()

            constructor(transFormula: TACTransFormula, cmd: HasTACCommand) :
                    this(transFormula, TACSummaryTag.TACCmdTag(cmd))
        }

        data class AssignmentSummary(
            override val transFormula: TACTransFormula,
            val lhs: TACExpr.Sym,
            val rhs: TACExpr,
            override val tag: TACSummaryTag
        ) : TACSummaryTransFormula() {
            override fun toString(): String = tag.toString()
        }

        data class AssertSummary(
            override val transFormula: TACTransFormula,
            val polarity: Boolean,
            val constraint: TACSymbol,
            override val tag: TACSummaryTag
        ) : TACSummaryTransFormula() {
            override fun toString(): String = tag.toString()
        }


        override fun copy(newTransFormula: TACTransFormula, newTag: TACSummaryTag): TACSummaryTransFormula =
            throw UnsupportedOperationException("Not implemented (need to double check why).")

        companion object {
            fun buildNop(cmd: HasTACCommand) = NopSummary(TACSummaryTag.TACCmdTag(cmd))
            fun buildNop(tag: TACSummaryTag) = NopSummary(tag)
        }

        override fun getTACSummaryTransformula(): TACSummaryTransFormula = this

        override fun toString(): String {
            return tag.toString()
        }
    }

    override fun summarizeLoop(loopBody: TACSummaryTransFormula): TACSummaryTransFormula {
        throw UnsupportedOperationException("Loops are not yet supported by transformula summarization. ($loopBody)")
    }
}
