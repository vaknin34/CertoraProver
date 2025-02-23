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

/**
 * Wraps a [CmdProcessor]; inserts some extra commands when certain commands are executed. E.g., on initialization and
 *  [reset], this does some basic setup, like setting the `:print-success` option.
 */
class ExtraCommandsCmdProcessor private constructor(val wrapped: CmdProcessor) : CmdProcessor by wrapped {

    private suspend fun basicSetup() {
        if (wrapped.options.printSuccess) {
            process(Cmd.SetOption(":print-success", "true")) // needed because CVC4 resets options
        }
        if (options.produceUnsatCores) {
            process(Cmd.SetOption(":produce-unsat-cores", "true"))
        }
        if (options.produceModels) {
            process(Cmd.SetOption(":produce-models", "true"))
        }
        if (options.queryDifficulties) {
            process(Cmd.SetOption(":produce-difficulty", "true"))
        }
    }

    /** needs special treatment, since, at least in CVC4, reset also reverts :print-success ... */
    override suspend fun reset(comment: String?) {
        wrapped.reset(comment)
        if (wrapped.options.incremental) {
            /* in non-incremental mode, [wrapped] is closed at this point */
            basicSetup()
        }
    }

    override fun toString(): String {
        return "ExtraCp($wrapped)"
    }

    override fun close() {
        wrapped.close()
    }

    companion object {
        suspend fun fromCommand(
            name: String,
            cmd: List<String>,
            options: CmdProcessor.Options,
            solverInstanceInfo: SolverInstanceInfo = SolverInstanceInfo.None,
            debugOutput: Boolean = false,
            crashOnError: Boolean = true,
            dumpFile: String? = null
        ): ExtraCommandsCmdProcessor {
            val interactingCmdProc = InteractingCmdProcessor.fromCommand(
                name,
                cmd,
                options,
                solverInstanceInfo = solverInstanceInfo,
                debugOutput = debugOutput,
                crashOnError = crashOnError
            )
            return ExtraCommandsCmdProcessor(
                if (dumpFile == null) {
                    interactingCmdProc
                } else {
                    TwoCmdProcessors(interactingCmdProc, PrintingCmdProcessor(dumpFile))
                }
            ).also { it.basicSetup() }
        }

        suspend fun fromSolverInstanceInfo(
            solverInstanceInfo: SolverInstanceInfo,
            dumpFile: String? = null,
        ) = fromCommand(
            name = solverInstanceInfo.name,
            cmd = solverInstanceInfo.actualCommand,
            options = solverInstanceInfo.options,
            solverInstanceInfo = solverInstanceInfo,
            dumpFile = dumpFile,
        )

        suspend fun fromCmdProcessor(
            cmdProcessor: CmdProcessor
        ) = ExtraCommandsCmdProcessor(cmdProcessor).also {
            it.basicSetup()
        }

    }
}
