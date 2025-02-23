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

package analysis.split

import analysis.CmdPointer
import analysis.LTACCmd
import scene.ITACMethod
import tac.MetaMap
import tac.TACBasicMeta
import utils.Color.Companion.bBlue
import utils.Color.Companion.bCyan
import utils.Color.Companion.black
import utils.Color.Companion.blue
import utils.Color.Companion.cyan
import utils.Color.Companion.green
import utils.Color.Companion.magenta
import utils.Color.Companion.red
import utils.Color.Companion.whiteBg
import utils.Color.Companion.yellow
import utils.Color.Companion.yellowBg
import vc.data.*

class SplitDebugger(
    private val cx: SplitContext,
    private val method: ITACMethod,
    private val varSplits: Map<TACSymbol.Var, Split> = mutableMapOf(),
    private val changes: Map<CmdPointer, List<TACCmd.Simple>> = mutableMapOf(),
) {

    /** When true then the meta info for the new commands is printed */
    private val withMeta = true

    private fun metaString(prefix: String, meta: MetaMap): String {
        val entries = meta.map.entries
            .filterNot { (m, _) ->
                m == META_INFO_KEY || m == TACBasicMeta.STACK_HEIGHT
            }
        return if (entries.isNotEmpty()) {
            "\n               $prefix ----> \n" +
                    entries.joinToString("\n") { (name, value) ->
                        "                     $name = $value"
                    }
        } else {
            ""
        }.magenta
    }

    private fun metaString(v: TACSymbol) =
        if (v is TACSymbol.Var) metaString(v.toString(), v.meta) else ""

    private fun metaString(e: TACExpr) =
        if (e is TACExpr.Sym) metaString(e.s) else ""

    /**
     * Entry point.
     */
    fun log() {
        cx.logger.debug(::generateMethodString)
    }

    private fun generateMethodString(): String {
        val sb = StringBuilder("\n")

        sb.appendLine("********************************************************")
        sb.appendLine("METHOD ${method.name.yellowBg.black}")
        sb.appendLine("********************************************************")
        sb.appendLine()

        val code = method.code as CoreTACProgram
        val dom = code.analysisCache.domination
        val blockIds = dom.topologicalOrder
        for (bid in blockIds) {
            sb.appendLine("NBId = ${bid.whiteBg.black}")
            sb.appendLine("----------------------------------------------------------")
            val cmds = code.analysisCache.graph.elab(bid).commands
            for (lcmd in cmds) {
                generateCmdString(sb, lcmd, method)
                changes[lcmd.ptr]?.let { cs ->
                    if (cs.isEmpty()) {
                        sb.appendLine("            ERASED".yellow)
                    } else {
                        cs.forEach { c ->
                            fun default() = c.toStringNoMeta()

                            val cmdMetaString = metaString("CMD", c.meta)
                            fun metaStrings(vararg es: TACExpr) = if (withMeta) {
                                cmdMetaString + es.joinToString("") { metaString(it) }
                            } else ""

                            fun metaStrings(vararg es: TACSymbol) = if (withMeta) {
                                cmdMetaString + es.joinToString("") { metaString(it) }
                            } else ""

                            val msg = when (c) {
                                is TACCmd.Simple.AssigningCmd.AssignExpCmd ->
                                    "${c.lhs} := ${c.rhs}${metaStrings(c.lhs.asSym(), c.rhs)}"

                                is TACCmd.Simple.AssigningCmd.WordLoad ->
                                    "${c.lhs} <- ${c.base}[${c.loc}]${metaStrings(c.lhs, c.base, c.loc)}"

                                is TACCmd.Simple.WordStore ->
                                    "${c.base}[${c.loc}] <- ${c.value}${metaStrings(c.base, c.loc, c.value)}"

                                is TACCmd.Simple.AssumeCmd ->
                                    "Assume ${c.cond}"

                                else ->
                                    default()
                            }
                            sb.appendLine("             ${msg.yellow}")

                        }
                    }
                }
            }
            sb.appendLine()
        }

        return sb.toString()
    }


    private fun generateCmdString(sb: StringBuilder, lCmd: LTACCmd, method: ITACMethod) {

        val (ptr, cmd) = lCmd

        val prefix = "${ptr.pos}:"

        fun default() =
            sb.appendLine("$prefix ${cmd.toStringNoMeta()}")

        fun TACSymbol.Var.inColor() =
            when {
                SplitContext.isKeywordVar(this) -> toString().bBlue
                this in (cx.mentionedVars[method] ?: emptySet()) -> toString().magenta
                else -> toString()
            }

        fun info(v: TACSymbol, t: Ternary) =
            when (v) {
                is TACSymbol.Var -> {
                    val s = varSplits[v]?.red ?: ""
                    "${v.inColor()} ${t.green} ${s.red}"
                }

                is TACSymbol.Const -> {
                    "$v".cyan
                }
            }

        fun lhsInfo() =
            info((cmd as TACCmd.Simple.AssigningCmd).lhs, cx.ternaries(method).getLhs(ptr))

        fun rhsInfo(v: TACSymbol) =
            info(v, cx.ternaries(method).getRhs(ptr, v.asSym()))

        when (cmd) {
            is TACCmd.Simple.JumpdestCmd,
            is TACCmd.Simple.LabelCmd,
            -> Unit

            is TACCmd.Simple.JumpCmd ->
                sb.appendLine("$prefix Jump ${cmd.dst.bCyan}")

            is TACCmd.Simple.JumpiCmd ->
                sb.appendLine("$prefix If ${cmd.cond.green} then ${cmd.dst.bCyan} else ${cmd.elseDst.bCyan}")

            is TACCmd.Simple.AnnotationCmd ->
                if (true /* cmd.mentionedVariables.isNotEmpty() */) {
                    sb.appendLine(
                        "$prefix Annotation ${cmd.annot.k} := ${cmd.annot.v} " +
                                "--> ${cmd.mentionedVariables.magenta}"
                    )
                }

            is TACCmd.Simple.AssigningCmd.WordLoad ->
                if (cx.isStorage(cmd.base)) {
                    sb.appendLine("$prefix ${lhsInfo()} <- ${"Storage[${cmd.loc}]".blue}")
                } else {
                    default()
                }

            is TACCmd.Simple.WordStore ->
                if (cx.isStorage(cmd.base)) {
                    sb.appendLine("$prefix ${"Storage[${cmd.loc}]".blue} <- ${rhsInfo(cmd.value)}")
                } else {
                    default()
                }

            is TACCmd.Simple.AssigningCmd.AssignExpCmd -> {
                if (SplitContext.isSimpleVar(cmd.lhs)) {
                    val c = cx.ternaries(method).getLhs(ptr).asConstantOrNull()
                    if (c != null) {
                        val cStr = "[" + when {
                            c < 10.toBigInteger() -> c.toString()
                            else -> "0x${c.toString(16)}"
                        } + "]"
                        sb.appendLine("$prefix ${cmd.lhs.inColor()} := ${cStr.magenta} ${cmd.rhs}")
                    } else {
                        sb.appendLine("$prefix ${lhsInfo()} := ${cmd.rhs}")
                    }
                } else {
                    default()
                }
            }

            else ->
                default()
        }
    }
}

