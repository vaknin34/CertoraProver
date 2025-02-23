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

import kotlinx.coroutines.flow.*
import smtlibutils.data.Cmd
import smtlibutils.data.SMT

/**
 * A [CmdProcessor] that just stores all the commands that it gets through the [process] methods for later processing.
 * This is used for example when we need to store the output of [LExpressionToSmtLib] for later processing, e.g., to do
 * purification for [CdclT].
 */
class CollectingCmdProcessor(
    private val cmds: MutableList<Cmd> = mutableListOf(),
    private var frozen: Boolean = false
) : CmdProcessor {

    override val solverInstanceInfo: SolverInstanceInfo
        get() = SolverInstanceInfo.None
    override val options: CmdProcessor.Options
        get() = CmdProcessor.Options.DontCare

    fun getResult(declarationsFirst: Boolean = false): SMT {
        frozen = true
        if (declarationsFirst) {
            val (setLogic, nonSetLogic) = cmds.partition { it is Cmd.SetLogic }

            val (declarations, nonSetLogicNonDecl) =
            nonSetLogic.partition { cmd ->
                cmd.let { it is Cmd.DeclareFun ||
                        it is Cmd.DeclareConst ||
                        it is Cmd.DeclareSort ||
                        it is Cmd.DefineFun } }

            val sortedLines = mutableListOf<Cmd>()
            sortedLines.addAll(setLogic)
            sortedLines.addAll(declarations)
            sortedLines.addAll(nonSetLogicNonDecl)

            return SMT(sortedLines)
        } else {
            return SMT(cmds)
        }
    }

    override fun processResult(cmd: Cmd): Flow<String> {
        check(!frozen)
        cmds.add(cmd)
        return emptyFlow()
    }

    override fun close() {
        frozen = true
    }

    /** Create a copy of this [CmdProcessor]. */
    fun fork(): CollectingCmdProcessor {
        return CollectingCmdProcessor(cmds.toMutableList(), frozen)
    }


}
