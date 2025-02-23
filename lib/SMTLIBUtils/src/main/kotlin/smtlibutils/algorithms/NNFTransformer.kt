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

package smtlibutils.algorithms

import smtlibutils.algorithms.ContainsIte.Companion.containsIte
import smtlibutils.data.Cmd
import smtlibutils.data.HasSmtExp
import smtlibutils.data.SmtExp
import smtlibutils.data.SmtIntpFunctionSymbol.Core
import smtlibutils.data.Sort

/**
 *
 * NB:
 *  - resolves [Core.Distinct] to negated [Core.Eq]
 */
class NNFTransformer : AndOrFlattener<NNFAcc>() {

    companion object {
        /**
         * (includes ite elimination)
         */
        fun nnfTransformCmd(hasExp: HasSmtExp): SmtExp {
            val exp = hasExp.exp
            check(exp.sort == Sort.BoolSort)

            // TODO (CERT-8094): this check avoids cases where IteEliminator crashes on a let expression
            // --> once lets are handled inside IteEliminator, we can remove this in favour of just the then-branch
            val iteEliminated = if (IteEliminator.hasAnyIte(exp)) IteEliminator.eliminateAllIte(exp) else exp

            return NNFTransformer().expr(iteEliminated, NNFAcc(false))
        }

        fun nnfTransformCmd(cmd: Cmd): Cmd = when (cmd) {
            is Cmd.NoOp -> cmd
            is Cmd.Goal, is Cmd.Model, is Cmd.ValDefList, is Cmd.Custom ->
                throw UnsupportedOperationException("$this: non nnf-able command: $cmd")
            is Cmd.Assert -> {
                cmd.copy(nnfTransformCmd(cmd.e))
            }
            is Cmd.DeclareSort -> cmd
            is Cmd.DeclareConst -> cmd
            is Cmd.DeclareFun -> cmd
            is Cmd.DeclareDatatypes -> cmd
            is Cmd.DefineFun -> {
                // TODO: if this occurs, implement inlining of define-funs on [SMT] level
                check(containsIte(cmd.definition)) {
                    "Found an ite inside a define-fun ($cmd); " +
                            "not supported right now"
                }
                cmd
            }
            is Cmd.CheckSat -> cmd
            is Cmd.GetModel -> cmd
            is Cmd.GetValue -> cmd
            is Cmd.GetInfo -> cmd
            is Cmd.GetUnsatCore -> cmd
            is Cmd.Reset -> cmd
            is Cmd.SetOption -> cmd
            is Cmd.SetLogic -> cmd
            is Cmd.StatsCmd -> cmd
            is Cmd.ResetAssertions -> cmd
            is Cmd.Push -> cmd
            is Cmd.Pop -> cmd
        }
    }

    override val cmdAccFactory: ((Cmd) -> NNFAcc) = { NNFAcc(false) }

    override fun expr(exp: SmtExp, acc: NNFAcc): SmtExp {
        assert(exp.sort != null) { "expression must be sorted for NNFTransformer to work" }
        return if (exp.isAtom()) {
            if (exp.isApp(Core.Distinct::class)) {
                expr(smtScript.apply(Core.Eq((exp as SmtExp.Apply).args[0].sort!!), exp.args), acc.flip())
            } else {
                if (acc.polarity) {
                    smtScript.apply(Core.LNot, listOf(exp))
                } else {
                    exp
                }
            }
        } else super.expr(exp, acc)
    }

    override fun letExp(exp: SmtExp.Let, acc: NNFAcc): SmtExp {
        check(exp.defs.all { it.def.sort != Sort.BoolSort })
        { "Boolean let expression should have been removed before NNF transformation" } // TODO think about it, this could be improved in the future (CERT-8094)
        return smtScript.letExpr(defs = exp.defs, body = expr(exp.body, acc))
    }

    override fun apply(exp: SmtExp.Apply, acc: NNFAcc): SmtExp {
        assert(!exp.isAtom())
        return when (exp.fs) {
            is Core.LNot -> {
                expr(exp.args[0], acc.flip())
            }
            is Core.LImplies -> {
                super.apply(Core.LOr,
                    listOf(
                        expr(exp.args[0], acc.flip()),
                        expr(exp.args[1], acc)),
                    exp.sort,
                    acc)
            }
            is Core.LAnd -> {
                if (acc.polarity) {
                    super.apply(Core.LOr, exp.args.map { arg: SmtExp -> expr(arg, acc) }, exp.sort, acc)
                } else {
                    super.apply(exp, acc)
                }
            }
            is Core.LOr -> {
                if (acc.polarity) {
                    super.apply(Core.LAnd, exp.args.map { arg: SmtExp -> expr(arg, acc) }, exp.sort, acc)
                } else {
                    super.apply(exp, acc)
                }
            }
            is Core.Eq -> {
                super.apply(
                    Core.LAnd, listOf(
                        super.apply(Core.LOr, listOf(expr(exp.args[0], acc.flip()), expr(exp.args[1], acc)), Sort.BoolSort, acc),
                        super.apply(Core.LOr, listOf(expr(exp.args[0], acc), expr(exp.args[1], acc.flip())), Sort.BoolSort, acc)
                    ),
                    exp.sort,
                    acc
                )
            }
            is Core.Distinct -> {
                super.apply(
                    Core.LOr, listOf(
                        super.apply(Core.LAnd, listOf(expr(exp.args[0], acc), expr(exp.args[1], acc.flip())), Sort.BoolSort, acc),
                        super.apply(Core.LAnd, listOf(expr(exp.args[0], acc.flip()), expr(exp.args[1], acc)), Sort.BoolSort, acc)
                    ),
                    exp.sort,
                    acc
                )
            }
            is Core.Ite -> error { "should have been removed beforehand " }
            else -> throw UnsupportedOperationException("failed to nnf expression \"$exp\"")
        }
    }

}

/**
 * @param polarity "false" means "we have seen an even of negations"
 *
 */
data class NNFAcc(val polarity: Boolean) {
    fun flip() = NNFAcc(!polarity)
}
