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

import log.*
import os.setCriticality
import java.io.File

object SubProcessInteraction {
    /**
     * Adapted from [https://stackoverflow.com/questions/35421699/how-to-invoke-external-command-from-within-kotlin-code#41495542]
     */
    fun runCommand(cmd: List<String>, workingDir: File, critical: Boolean): Process {
        logger.debug { "running command \"$cmd\" in directory \"$workingDir\"" }
        return ProcessBuilder(*cmd.toTypedArray())
            .directory(workingDir)
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
            .redirectError(ProcessBuilder.Redirect.PIPE)
            .start()
            .apply { setCriticality(critical) }
    }

    private val logger = Logger(SMTLIBUtilsLoggerTypes.SMTLIBUTILS)

}
