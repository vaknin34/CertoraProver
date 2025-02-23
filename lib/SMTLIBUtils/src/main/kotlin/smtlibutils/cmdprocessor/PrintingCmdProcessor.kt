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
import log.*
import smtlibutils.data.Cmd
import utils.ArtifactFileUtils
import java.io.PrintWriter


class PrintingCmdProcessor(
    val filename: String,
    override val options: CmdProcessor.Options = CmdProcessor.Options.Default.copy(noAnswers = true),
    val prettyPrinter: SmtPrettyPrinter = SmtPrettyPrinter.DiffFriendly(),
    private val commentOutPrintSuccess: Boolean = true
) : CmdProcessor {
    init {
        if (!options.noAnswers) {
            logger.warn { "created a PrintingCmdProcessor with \"noAnswers\" option set to false -- unexpected." }
        }
    }

    override val solverInstanceInfo: SolverInstanceInfo
        get() = SolverInstanceInfo.None

    private val pw =
        try {
            PrintWriter(ArtifactFileUtils.getWriterForFile(filename, overwrite = true))
        } catch (e: Exception) {
            logger.error(e) { "failed to create file $filename; not printing to that file" }
            null
        }


    /**
     * set [addLineBreakWhenCommenting] to ensure the line comment doesn't influence anything else in a line with more
     * than one command
     */
    private fun prettyPrintCommand(cmd: Cmd): String {
        val cmdString = prettyPrinter.prettyPrint(cmd)
        return if (commentOutPrintSuccess && cmd is Cmd.SetOption && cmd.name == ":print-success") {
            "; $cmdString"
        } else {
            cmdString
        }
    }

    override fun processResult(cmd: Cmd) = flow<String> {
        pw?.apply {
            println(prettyPrintCommand(cmd))
            if (isFlushingCmd(cmd)) {
                flush()
            }
        }
    }

    /**
     * We're flushing every now and then, since the formula output can be important during debugging a
     *  solver timeout (and when the user interrupts the solver, the flush may not have happened automatically since
     *  [close] may not have been called..).
     */
    private fun isFlushingCmd(cmd: Cmd): Boolean =
        cmd !is Cmd.DeclareFun && cmd !is Cmd.DefineFun && cmd !is Cmd.Assert

    override fun close() {
        if (pw == null) return
        pw.flush()
        pw.close()
    }
}

private val logger = Logger(SMTLIBUtilsLoggerTypes.SMTLIBUTILS)
