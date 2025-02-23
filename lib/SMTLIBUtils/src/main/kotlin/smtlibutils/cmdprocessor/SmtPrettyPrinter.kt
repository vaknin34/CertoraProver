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

package smtlibutils.cmdprocessor

import smtlibutils.data.Cmd
import smtlibutils.data.SmtExp
import utils.`impossible!`

sealed interface SmtPrettyPrinter {
    /** Converts a command into a list of strings (each string representing a line) . */
    fun prettyPrint(cmd: Cmd): String

    object Trivial : SmtPrettyPrinter {
        override fun prettyPrint(cmd: Cmd): String = cmd.toString()
    }

    class DiffFriendly(private val indent: String = "  ") : SmtPrettyPrinter {

        override fun prettyPrint(cmd: Cmd): String {
            val res = when (cmd) {
                is Cmd.Assert -> {
                    "(${Cmd.Assert.keyword}\n" +
                            "$indent${prettyPrint(cmd.e, 2)}\n" +
                            ")" + (cmd.comment?.let { " ; $it" } ?: "")
                }
                is Cmd.DefineFun -> {
                    "(${Cmd.DefineFun.keyword}\n" +
                        "$indent${cmd.name}\n" +
                        "$indent(${cmd.params.joinToString(" ")})\n" +
                        "$indent${cmd.res_sort}\n" +
                        "$indent${prettyPrint(cmd.definition, 2)}\n" +
                        ")" + (cmd.comment?.let { " ; $it" } ?: "")
                }
                else -> cmd.toString()
            }
            return res
        }

        private fun prettyPrint(exp: SmtExp, nestingDepth: Int): String = prettyPrintRec(exp, nestingDepth).first

        /** The second entry in the return type is used to assess whether the returned expression is "small".
         * "small" expressions don't trigger line breaks and indentation like the others do. */
        private fun prettyPrintRec(exp: SmtExp, nestingDepth: Int): Pair<String, Boolean> {
            val res: Pair<String, Boolean> = when (exp) {
                is SmtExp.AnnotatedExp -> {
                    val i0 = indent.repeat(nestingDepth - 1)
                    val i1 = indent.repeat(nestingDepth)
                    "(!\n" +
                            "$i1${prettyPrintRec(exp.innerExp, nestingDepth + 1).first}\n" +
                            "$i1${exp.annotation}\n" +
                            "$i0)" to false
                }
                is SmtExp.Apply ->
                    exp.args.map { prettyPrintRec(it, nestingDepth + 1) }.let { argToIsSimple ->
                        if (argToIsSimple.map { it.second }.all { it }) {
                            exp.toString() to false
                        } else {
                            val argsStrings = argToIsSimple.map { it.first }
                            val fs = exp.fs
                            val i0 = indent.repeat(nestingDepth - 1)
                            val i1 = indent.repeat(nestingDepth)
                            if (exp.isConstant) {
                                fs.toString() to true
                            } else {
                                "(${fs.toSMTLIBString()}\n$i1${argsStrings.joinToString("\n$i1")}\n$i0)" to false
                            }
                        }
                    }
                is SmtExp.Quant -> {
                    val i0 = indent.repeat(nestingDepth - 1)
                    val i1 = indent.repeat(nestingDepth)
                    val i2 = indent.repeat(nestingDepth + 1)
                    "(${exp.quantString}\n" +
                            "$i1(${exp.boundVars.joinToString(i2)})\n" +
                            "$i1${prettyPrintRec(exp.body, nestingDepth + 1).first}\n" +
                            "$i0)" to false
                }
                is SmtExp.BitvectorLiteral,
                is SmtExp.BoolLiteral,
                is SmtExp.DecLiteral,
                is SmtExp.IntLiteral,
                is SmtExp.Lambda,
                is SmtExp.Let,
                is SmtExp.QualIdentifier -> exp.toString() to true
                is SmtExp.PlaceHolder -> `impossible!`
            }
            return res
        }
    }
}
