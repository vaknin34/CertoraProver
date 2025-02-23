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

package vc.data.tacexprutil

import tac.MetaKey
import vc.data.TACExpr
import java.io.Serializable

/**
 * Brings a [TACExpr] into somewhat (more) readable form that the standard toString, in particular if it's larger.
 * No plans of being able to parse these again.
 *
 * Possible improvements:
 *  - Formatting could be made dependent on the size of the operand results (make a line break if they're large).
 *  - prettier representations for expressions that get no special treatment so far
 */
object TACExprPrettyPrinter : AccumulatingTACExprTransFormerWithDefaultRes<TACExprPrettyPrinter.Acc, String>() {

    private const val indent = "  "

    fun print(e: TACExpr): String = this.transform(Acc(0), e)

    /**
     * @param indents the base indentation of the to-be printed expression -- nothing may be indented less than this,
     *          subexpressions more, has to be inserted after each line break
     */
    @JvmInline
    value class Acc(val indents: Int) {
        operator fun plus(i: Int) = Acc(indents + i)
    }
    override fun defaultRes(acc: Acc, e: TACExpr): String = "$e"

    private fun indnt(acc: Acc) = indent.repeat(acc.indents)

    override fun transformMapDefinition(acc: Acc, exp: TACExpr.MapDefinition): String {
        return "{${exp.defParams} ->\n" +
            "${indnt(acc + 1)}${transform(acc + 1, exp.definition)}\n" +
            "${indnt(acc)}}"
    }

    override fun transformIte(acc: Acc, e: TACExpr.TernaryExp.Ite): String {
        return "Ite(\n" +
            "${indnt(acc + 1)}${transform(acc + 1, e.i)}\n" +
            "${indnt(acc + 1)}${transform(acc + 1, e.t)}\n" +
            "${indnt(acc + 1)}${transform(acc + 1, e.e)}\n" +
            "${indnt(acc)})"
    }

    override fun transformEq(acc: Acc, e: TACExpr.BinRel.Eq): String =
        "${transform(acc, e.o1)} == ${transform(acc, e.o2)}"

    override fun transformGt(acc: Acc, e: TACExpr.BinRel.Gt): String =
        "${transform(acc, e.o1)} > ${transform(acc, e.o2)}"

    override fun transformGe(acc: Acc, e: TACExpr.BinRel.Ge): String =
        "${transform(acc, e.o1)} >= ${transform(acc, e.o2)}"

    override fun transformLt(acc: Acc, e: TACExpr.BinRel.Lt): String =
        "${transform(acc, e.o1)} < ${transform(acc, e.o2)}"

    override fun transformLe(acc: Acc, e: TACExpr.BinRel.Le): String =
        "${transform(acc, e.o1)} <= ${transform(acc, e.o2)}"

    override fun <T : Serializable> transformAnnotationExp(acc: Acc, o: TACExpr, k: MetaKey<T>, v: T): String =
        "Annot(${transform(acc, o)},$k := $v)"

}
