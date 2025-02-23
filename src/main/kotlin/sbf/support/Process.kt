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

package sbf.support

import java.io.File
import java.nio.file.Path
import java.nio.file.Paths

// this function is borrowed from MutationTesting code
fun runCommand(
        args: List<String>,
        stdin: String,
        workingDir: Path = Paths.get("."),
        script: File? = null
    ): Triple<String, String, Int> {
        val process = ProcessBuilder(*args.toTypedArray())
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
            .redirectInput(ProcessBuilder.Redirect.PIPE)
            .redirectError(ProcessBuilder.Redirect.PIPE)
            .directory(workingDir.toFile())
            .start()
        val procOutput = process.outputStream.bufferedWriter()
        val procInput = process.inputStream.bufferedReader()
        val procError = process.errorStream.bufferedReader()
        procOutput.write(stdin)
        if (script != null) {
            script.reader().transferTo(procOutput)
            procOutput.write("\n")
        }
        procOutput.flush()
        procOutput.close()
        val res = procInput.readText()
        procInput.close()
        val error = procError.readText()
        procError.close()
        val exitcode = process.waitFor()
        return Triple(res, error, exitcode)
    }
