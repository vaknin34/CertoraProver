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

import smtlibutils.algorithms.IteEliminator.Mode
import smtlibutils.data.*
import smtlibutils.data.SmtIntpFunctionSymbol.Core

/**
 * Transforms an [SMT] Ast into an [SMT] Ast without ite terms ([SmtIntpFunctionSymbol.Core.Ite]).
 *
 * Ite's can be resolved in either of two ways:
 *  - conjunction of disjunctions [Mode.CONJUNCTION]
 *  - disjunction of conjunctions [Mode.DISJUNCTION]
 *
 *  Algorithmic plan:
 *   - Always remove one ite at a time, there are no more ite's when the output of [IteEliminator] equals its input.
 *
 */
class IteEliminator(val mode: Mode = Mode.DISJUNCTION) :
    TransformSmtWithResult<IteEliminator.Context, IteEliminator.CmdRes, IteEliminator.ExpRes>() {
    enum class Mode { CONJUNCTION, DISJUNCTION; }

    companion object {
        fun eliminateAllIte(exp: SmtExp, mode: Mode = Mode.DISJUNCTION): SmtExp {
            check(exp.sort == Sort.BoolSort)
            var res = exp
            do {
                val iteEliminator = IteEliminator(mode)
                res = iteEliminator.expr(res, Context(false)).exp
            } while (iteEliminator.changedSomething)
            return res
        }

        /** Returns true iff there is an [Core.Ite] application in [exp]. */
        fun hasAnyIte(exp: SmtExp): Boolean {
            val trav = object : TraverseSmt() {
                var foundIte = false
                override fun apply(exp: SmtExp.Apply) {
                    if (exp.fs is Core.Ite) foundIte = true
                    super.apply(exp)
                }
            }
            trav.expr(exp)
            return trav.foundIte
        }
    }

    var changedSomething = false

    override val expERFactory: (SmtExp) -> ExpRes = { exp -> ExpRes.NoIte(exp) }
    override val cmdCRFactory: (Cmd) -> CmdRes
        get() = throw UnsupportedOperationException("Not yet implemented")

    override fun apply(exp: SmtExp.Apply, acc: Context): ExpRes {
        return if (acc.insideAtom) {
            if (exp.isApp(Core.Ite::class)) {
                val placeHolder =
                    smtScript.qualIdentifier(smtScript.simpleIdentifier("__iteReplacement"), null, exp.sort)
                return ExpRes.IteInAtomic(
                    placeHolder,
                    exp.args[0],
                    exp.args[1],
                    exp.args[2],
                    placeHolder
                )
            } else {
                val el = mutableListOf<SmtExp>()
                exp.args.forEachIndexed { index, arg ->
                    val argRes = expr(arg, acc)
                    el.add(argRes.exp)
                    if (argRes is ExpRes.IteInAtomic) {
                        el.addAll(exp.args.subList(index + 1, exp.args.size))
                        return@apply argRes.copy(exp = super.smtScript.apply(exp.fs, el, exp.sort))
                    }
                }
                check(el.size == exp.args.size)
                expERFactory(super.smtScript.apply(exp.fs, el, exp.sort))

            }
        } else if (exp.isAtom()) {
            /** crossing over from Boolean to atom-level */
            check(!acc.insideAtom)
            // nb: we change the context for this apply-call, thus this should not lead to an endless recursion
            when (val res = apply(exp, Context(true))) {
                is ExpRes.IteInAtomic -> {
                    val cnd = res.cond
                    val thn = Substitutor(mapOf(res.placeHolder to res.thenBranch)).expr(res.exp, Unit)
                    val els = Substitutor(mapOf(res.placeHolder to res.elseBranch)).expr(res.exp, Unit)
                    changedSomething = true
                    ExpRes.NoIte(buildIteReplacement(cnd, thn, els))
                }
                is ExpRes.NoIte -> res
            }
        } else {
            /** we're on Boolean level */
            if (exp.isApp(Core.Ite::class)) {
                changedSomething = true
                ExpRes.NoIte(buildIteReplacement(exp.args[0], exp.args[1], exp.args[2]))
            } else {
                super.apply(exp, Context(exp.isAtom())) // TODO review
            }
        }
    }

    private fun buildIteReplacement(
        cond: SmtExp,
        thn: SmtExp,
        els: SmtExp
    ): SmtExp.Apply {
        val res = when (mode) {
            /* ite A B C -> (or (and A B) (and (not A) C))) */
            Mode.DISJUNCTION -> smtScript.apply(
                Core.LOr, listOf(
                    smtScript.apply(Core.LAnd, listOf(cond, thn)),
                    smtScript.apply(Core.LAnd, listOf(smtScript.apply(Core.LNot, listOf(cond)), els))
                )
            )
            /* ite A B C -> (and (or (not A) B) (or A C))) */
            Mode.CONJUNCTION -> smtScript.apply(
                Core.LAnd, listOf(
                    smtScript.apply(Core.LOr, listOf(smtScript.apply(Core.LNot, listOf(cond)), thn)),
                    smtScript.apply(Core.LOr, listOf(cond, els))
                )
            )
        }
        return res
    }

    override fun forallExp(exp: SmtExp.Quant.ForAll, acc: Context): ExpRes =
        error("$this: quantifiers not supported right now")

    override fun existsExp(exp: SmtExp.Quant.Exists, acc: Context): ExpRes =
        error("$this: quantifiers not supported right now")

    override fun letExp(exp: SmtExp.Let, acc: Context): ExpRes = error("$this: let not supported right now")

    override fun lambda(exp: SmtExp.Lambda, acc: Context): ExpRes = error("$this: lambda not supported right now")

    class Context(val insideAtom: Boolean) //TODO .. or would "insideLiteral" be better, in order to preserve NNF?

    class CmdRes(override val cmd: Cmd) : TransformSmtResultCmd

    sealed class ExpRes : TransformSmtResultExp {
        /** When we see an ite in an atomic formula, we need to carry information about it to the Boolean level;
         * that is the purpose of this class. */
        data class IteInAtomic(
            override val exp: SmtExp,
            val cond: SmtExp,
            val thenBranch: SmtExp,
            val elseBranch: SmtExp,
            val placeHolder: SmtExp.QualIdentifier
        ) :
            ExpRes()

        /** default case */
        data class NoIte(override val exp: SmtExp) : ExpRes()
    }

}
