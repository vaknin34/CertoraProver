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

import algorithms.computeCrossProduct
import smtlibutils.data.*

class DNFTransformer : TransformSmtWithResult<Unit, DNFTransformer.CmdRes, DNFTransformer.ExpRes>() {

    class DNF(val li: MutableList<List<SmtExp>>) {
        companion object {
            fun literal(exp: SmtExp): DNF = DNF(mutableListOf(mutableListOf(exp)))
        }

        fun mergeDisj(other: DNF): DNF = apply { li.addAll(other.li) }

        fun mergeConj(other: DNF): DNF = apply {
            val productLi =
                computeCrossProduct(this.li, other.li) { l1: List<SmtExp>, l2: List<SmtExp> -> l1 + l2 }
            this.li.clear()
            this.li.addAll(productLi)
        }

        fun toExp(smtScript: ISmtScript): SmtExp =
            smtScript.or(
                *li.map {
                    smtScript.and(*it.toTypedArray())
                }.toTypedArray()
            )
    }

    companion object {
        /**
         * assumes exp is in NNF (implies no ite, distinct, implies, etc..)
         */
        fun transformToDNF(exp: SmtExp): DNF {
            check(exp.sort == Sort.BoolSort)
            val transformer = DNFTransformer()
            val res = transformer.expr(exp, Unit)
            return res.dnf
        }
    }

    override fun expr(exp: SmtExp, acc: Unit): ExpRes {
        return if (exp.isBooleanLiteral()) {
            ExpRes(DNF.literal(exp))
        } else {
            when (exp) {
                is SmtExp.Apply -> when (exp.fs) {
                    is SmtIntpFunctionSymbol.Core.LOr ->
                        ExpRes(exp.args.map { expr(it, Unit).dnf }.reduce { dnf1, dnf2 -> dnf1.mergeDisj(dnf2) })
                    is SmtIntpFunctionSymbol.Core.LAnd ->
                        ExpRes(exp.args.map { expr(it, Unit).dnf }.reduce { dnf1, dnf2 -> dnf1.mergeConj(dnf2) })
                    else -> error { "should not happen" }
                }
                else -> error { "should not happen" }
            }
        }
    }

    class CmdRes(override val cmd: Cmd) : TransformSmtResultCmd

    class ExpRes(val dnf: DNF) : TransformSmtResultExp {
        override val exp: SmtExp
            get() = throw UnsupportedOperationException("not implemented") // old: dnf.toExp() -- misses argument though
    }

    override val expERFactory: (SmtExp) -> ExpRes
        get() = throw UnsupportedOperationException("Not yet implemented")
    override val cmdCRFactory: (Cmd) -> CmdRes
        get() = throw UnsupportedOperationException("Not yet implemented")
}
