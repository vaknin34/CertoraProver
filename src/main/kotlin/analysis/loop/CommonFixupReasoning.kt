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

package analysis.loop

import analysis.*
import analysis.dataflow.IMustEqualsAnalysis
import analysis.smtblaster.*
import evm.EVM_ARRAY_ELEM_OFFSET
import parallel.*
import parallel.Scheduler.rpc
import smtlibutils.data.SmtExp
import tac.NBId
import tac.Tag
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol
import vc.data.tacexprutil.DefaultTACExprTransformer
import vc.data.tacexprutil.TACExprTransformer
import java.math.BigInteger

interface FixupAccessTagging {
    val outputAccess: Set<CmdPointer>
    val inputAccess: Set<CmdPointer>
}

data class FixupBlockResult(
    val fixupEnd: CmdPointer,
    override val outputAccess: Set<CmdPointer>,
    override val inputAccess: Set<CmdPointer>,
) : FixupAccessTagging

interface FixupBlockChecker {
    fun checkFixupBlock(scriptGen: Generator, destBlock: TACBlock, localState: MutableMap<TACSymbol.Var, TACExpr>, localMapper: TACExprTransformer<TACExpr>): Parallel<FixupBlockResult?>

    fun stepSymbolic(mapper: TACExprTransformer<TACExpr>, state: MutableMap<TACSymbol.Var, TACExpr>, c: LTACCmd): Boolean {
        if (c.cmd is TACCmd.Simple.JumpdestCmd || c.cmd is TACCmd.Simple.JumpiCmd || c.cmd is TACCmd.Simple.NopCmd) {
            return true
        }
        if (c.cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
            if (c.cmd is TACCmd.Simple.LabelCmd || c.cmd is TACCmd.Simple.NopCmd || c.cmd is TACCmd.Simple.AnnotationCmd) {
                return true
            }
            return false
        }
        state[c.cmd.lhs] = mapper.transform(c.cmd.rhs)
        return true
    }
}

class Generator(private val generate: () -> SmtExpScriptBuilder, private val actions: List<(SmtExpScriptBuilder) -> Unit>) {
    fun bind(f: (SmtExpScriptBuilder) -> Unit) : Generator {
        return Generator(generate, actions + f)
    }

    fun build(): SmtExpScriptBuilder {
        return actions.fold(generate()) { acc, f ->
            f(acc)
            acc
        }
    }

    fun fork() = Generator(generate, actions)
}

abstract class CommonFixupReasoning(
    protected val zBlaster: IBlaster,
    protected val builder: AbstractSmtExpTermBuilder,
    private val me: IMustEqualsAnalysis
) : AbstractArraySummaryExtractor(), FixupBlockChecker {

    sealed class PostWriteFixup : FixupAccessTagging {

        /** When the fixup block is conditionally executed */
        data class ConditionalFixup(
            val fixupBlocks: Set<NBId>,
            val succBlock: NBId,
            override val outputAccess: Set<CmdPointer>,
            override val inputAccess: Set<CmdPointer>
        ) : PostWriteFixup()

        /** When the fixup code is in the same block as the copy loop successor */
        data class SplitFixup(val finalWrite: CmdPointer, override val outputAccess: Set<CmdPointer>, override val inputAccess: Set<CmdPointer>) : PostWriteFixup()
    }

    /**
     * A class to hold the functions [preExit] and [postExit] that give the symbolic value of a variable before and after
     * the "final" loop iteration respectively.
     *
     * Specifically, suppose there is an instrumented variable `count` which is the
     * loop iteration counter, i.e. at the beginning of the loop `count` is 0, on th next iteration it is 1, etc.
     * The "final" loop iteration is the smallest value of `count` at which the loop body is *not* entered, i.e. the loop condition
     * is false. Call this number `post`. Assuming that the value of a variable after n iterations can be
     * expressed as a function of the number of iterations, f(i), then the symbolic representation of that variable
     * after the final iteration is simply the expansion of `f(post)`. The symbolic representation of that variable after
     * the loop exits is just `f(post - 1)` (from our definition of final, the loop is definitely entered at all loop iterations
     * smaller than `post`, by definition).
     *
     * Although not expressed in the type, it is expected that the functions [postExit] and [preExit] will, where possible,
     * express the values of these variables in terms of the variables assigned loop roles as recorded in the [analysis.loop.ArrayLoopSummarization.WriteEvery]
     * objects.
     *
     * Because [postExit] and [preExit] are *total* functions, they must give reasonable expressions for all variables,
     * including those that do not have closed forms or which are not expressed in terms of loop roles. This may require
     * the introducion of dummy free variables, which must be included in the smt scripts that these expressions are ultimately
     * encoded into. Thus, the [builder] function is a callback to be used by clients which is guaranteed to register the free variables
     * generated by [postExit] and [preExit] *up to that point*. It is expected that you will not call [postExit] or [preExit]
     * after "finalizing" the script by calling [builder].
     */
    class LoopInstantiations(val postExit: (TACSymbol.Var) -> TACExpr, val preExit: (TACSymbol.Var) -> TACExpr, val builder: (SmtExpScriptBuilder, ExpressionTranslator<SmtExp>) -> SmtExpScriptBuilder)

    /**
     * Produce [LoopInstantiations] mapping loop variables to their symbolic values pre/post loop exit.
     * @param l the Loop we're considering
     * @param loopSummarization the summary from which to produce the substitutions
     * @param w the loop's access summary
     * @return the loop instantiations
     */
    private fun loopInstantiations(l: Loop, loopSummarization: LoopSummarization.LoopIterationSummary, w: ArrayLoopSummarization.WriteEvery): LoopInstantiations? {

        val monotoneSyms = mutableMapOf<TACSymbol.Var, Pair<String, TACExpr>>()
        val finalIter = TACSymbol.Var(namePrefix = "finalWrite", tag = Tag.Bit256)
        val freeVars = mutableSetOf(finalIter.namePrefix)
        val closedForm = interpolateLoop(loopSummarization) ?: return null
        val postExitInstantiation: (TACSymbol.Var) -> TACExpr = {
            val loopIteration = finalIter.asSym()
            instantiate(w, it, freeVars, monotoneSyms, closedForm, loopIteration, l)
        }
        val preExitInstantiator: (TACSymbol.Var) -> TACExpr = {
            instantiate(w, it, freeVars, monotoneSyms, closedForm, TACExpr.BinOp.Sub(finalIter.asSym(), TACSymbol.lift(1).asSym()), l)
        }

        return LoopInstantiations(postExitInstantiation, preExitInstantiator) { smtCommands_, blaster ->
            val smtCommands = smtCommands_.fork()
            for (fv in freeVars) {
                smtCommands.declare(fv)
            }

            axiomatizeFunctions(smtCommands, monotoneSyms.values) {
                blaster.blastExpr(it, TACSymbol.Var::toSMTRep)
            }
            smtCommands
        }
    }

    /**
     * Loop expressions instantiated with loop roles
     * @param exit The post-exit instantiation applied to the loop exit condition
     * @param preExit The pre-exit instantiation applied to the loop exit condition
     * @param preExitWrite The pre-exit instantiation applied to the final write index
     */
    data class LoopConditions(val exit: SmtExp, val preExit: SmtExp, val preExitWrite: SmtExp)

    /**
     * Apply the loop instantiations to the exit condition and write index. The smt script builder
     * generator returned on success will contain constraints such that the `post` value mentioned in the documentation
     * of [LoopInstantiations] is constrained to be the actual last iteration.
     *
     * @param loopSummarization the loop we're considering
     * @param loopInst the loop expressions to instantiate
     * @param writeIndex the [TACExpr] corresponding to the index of the copy loop write
     *
     * @return the pair (smt, loop instantiations) on success
     */
    private fun instantiateAndAssertLoopExit(loopSummarization: LoopSummarization.LoopIterationSummary, loopInst: LoopInstantiations, writeIndex: TACExpr): Pair<Generator, LoopConditions>? {
        val postExitInstantiation = loopInst.postExit
        val preExitInstantiator = loopInst.preExit

        val blaster = ExpressionTranslator(builder, List<SmtExp>::toTypedArray)

        /**
         * Recall that these conditions are symbolic w.r.t. the `post` special value.
         */
        val exitCond = blaster.blastExpr(instantiateExpr(loopSummarization.exitCondition, postExitInstantiation)) {
            it.toSMTRep()
        } ?: return null

        val preExitCond = blaster.blastExpr(instantiateExpr(loopSummarization.exitCondition, preExitInstantiator)) {
            it.toSMTRep()
        } ?: return null

        val preExitWrite = blaster.blastExpr(instantiateExpr(writeIndex, preExitInstantiator)) {
            it.toSMTRep()
        } ?: return null
        val generator = Generator({ ->
            /**
             * Generate a fresh smt script builder, and have the free variables and monotone functions axiomatized
             * by the builder in [loopInst]
             */
            val smtCommands = loopInst.builder(SmtExpScriptBuilder(builder), blaster)
            Companion.addAxioms(smtCommands, BigInteger.ONE, elemStartOffset = EVM_ARRAY_ELEM_OFFSET)
            /**
             * Assert that our model must have that at iteration `post` the exit condition is not equal to 0 (aka true)...
             */
            smtCommands.assert {
                lnot(eq(exitCond, const(0)))
            }
            /**
             * but at the previous iteration the condition is equal to 0 (aka false). The only possible model for which this
             * is true is the one where `post` is the loop iteration on which the loop is exited.
             *
             * NB that in the above I said exit condition, *not* loop condition.
             */
            smtCommands.assert {
                eq(preExitCond, const(0))
            }
            smtCommands
        }, listOf())


        return (generator to LoopConditions(exitCond, preExitCond, preExitWrite))
    }

    /* Build an expr transformer that applies the given loop instantiation (i.e. variable to loop role substitution) */
    fun makeStateMapper(state: MutableMap<TACSymbol.Var, TACExpr>, instantiations: LoopInstantiations): DefaultTACExprTransformer {
        return object : DefaultTACExprTransformer() {
            override fun transform(exp: TACExpr): TACExpr {
                return if (exp is TACExpr.Sym.Var) {
                    state.computeIfAbsent(exp.s) {
                        instantiateExpr(exp, instantiations.postExit)
                    }
                } else {
                    super.transform(exp)
                }
            }
        }
    }

    /* Checks if we potentially overwrote in the last loop iteration and then calls the [onInexact] continuation if so. */
    fun <T> whenPreExitWriteInexact(smtCommands: Generator, loopConds: LoopConditions, onInexact: () -> Parallel<T?>): BindJob<T?> {
        val preExitWrite = loopConds.preExitWrite
        // now see what we can infer about the pre-exit write
        val exactWrites = smtCommands.bind { exactWrites ->
            // see if we can prove whether final write was exact
            exactWrites.assert {
                lnot(eq(toIdent(LoopRole.END.name), plus(const(32), preExitWrite)))
            }
            exactWrites.checkSat()
        }.build()
        return rpc {
            !zBlaster.blastSmt(exactWrites.cmdList)
        }.bindFalseAsNull {
            /* so we potentially overwrote in this branch, let's check */
            // okay, now let's see if we overwrite, and if so, whether we write 0 at the end pointer
            val overWrite = smtCommands.bind { overWrite ->
                overWrite.assert {
                    le(toIdent(LoopRole.ELEM_START.name), plus(preExitWrite, const(32)))
                }
                overWrite.assert {
                    ge(toIdent(LoopRole.END.name), plus(preExitWrite, const(32)))
                }
                overWrite.checkSat()
            }.build()
            rpc {
                zBlaster.blastSmt(overWrite.cmdList)
            }.bindFalseAsNull(onInexact)
        }
    }

    /**
     * Given the instantiations of the loop conditions and write index in [loopConds], and the
     * instantation functions in [loopInstantiations], is the sole loop success of [soleSuccBlock] a post write fixup?
     *
     * The [smtCommandGen] function should be used by implementers to get smt scripts that have free variables properly
     * declared/axiomatized and can be later extended to discharge fixup specific queries.
     */
    abstract fun findPostWriteFixup(
        g: TACCommandGraph,
        smtCommandGen: Generator,
        soleSuccBlock: TACBlock,
        loopConds: LoopConditions,
        loopInstantiations: LoopInstantiations
    ): Parallel<PostWriteFixup?>?

    /**
     * Returns a parallel job which, indicates that a loop [l] with summary [loopSummarization] and and a known write stride [w]
     * performs a post write fixup at the indicated location.
     */
    fun isPostWriteFixup(l: Loop, loopSummarization: LoopSummarization.LoopIterationSummary, w: ArrayLoopSummarization.WriteEvery, g: TACCommandGraph): Parallel<PostWriteFixup?> = Scheduler.forkOrNull fork@{
        if (w.assumedSize != BigInteger.ONE) {
            return@fork null
        }
        if (loopSummarization.isDoLoop) {
            return@fork null
        }
        val instantiations = loopInstantiations(l, loopSummarization, w) ?: return@fork null
        val (smtCommands, conds) = instantiateAndAssertLoopExit(loopSummarization, instantiations, w.write.index)
                ?: return@fork null

        val revertBlock = g.cache.revertBlocks
        val soleSucc = l.body.flatMap {
            g.succ(it) - l.body - revertBlock
        }.singleOrNull() ?: return@fork null
        val soleSuccBlock = g.elab(soleSucc)

        findPostWriteFixup(g, smtCommands, soleSuccBlock, conds, instantiations)
    }

    /**
     * Give the symbolic representation of the variable [it] at the [loopIteration] iteration.
     *
     * If [it] has a loop role in [w] and a mutation in [closedForm], then this function
     * will return the mutation w.r.t. the symbolic name of that role. Otherwise, a dummy "PRE_LOOP" variable
     * is generated.
     */
    private fun instantiate(
        w: ArrayLoopSummarization.WriteEvery,
        it: TACSymbol.Var,
        freeVars: MutableSet<String>,
        monotoneSyms: MutableMap<TACSymbol.Var, Pair<String, TACExpr>>,
        closedForm: Map<TACSymbol.Var, Interpolation>,
        loopIteration: TACExpr,
        loop: Loop
    ): TACExpr {
        val startRole = me.withEquivBefore(CmdPointer(loop.head, 0)) {
            it.equivOf().mapNotNull {
                w.roles.get(it)
            }
        }.toSet().singleOrNull()?.let {
            TACSymbol.Var(namePrefix = it.name, tag = Tag.Bit256)
        } ?: run {
            val ret = it.copy(namePrefix = it.namePrefix + "_CERTORA_PRE")
            freeVars.add(ret.namePrefix)
            ret
        }
        val closed = closedForm[it] ?: Interpolation.Identity
        return instantiateExpressionAt(it, start = startRole.asSym(), functionSymbols = monotoneSyms, interp = closed, loopIteration = loopIteration)
    }

    protected open fun plasusibleFixupBlock(b: TACBlock): Boolean {
        return b.commands.any {
            it.cmd is TACCmd.Simple.AssigningCmd.ByteStore
        }
    }

}
