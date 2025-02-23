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

import sbf.sbfLogger
import datastructures.stdcollections.*
import kotlin.io.path.absolutePathString

/**
 *  Demangle the list of symbols using rustfilt.
 *  Hashes are stripped so the function demangle is NOT an injective function.
 */
fun demangle(symbols: List<String>): List<String>? {
    val inFile  = kotlin.io.path.createTempFile("cvt_demangle_input").absolutePathString()
    val outFile = kotlin.io.path.createTempFile("cvt_demangle_input").absolutePathString()

    // Prepare input file
    var fileStr = ""
    for (s in symbols) {
        fileStr += "$s\n"
    }
    printToFile(inFile, fileStr, true)

    // Call external process for rustfilt
    runCommand(listOf("rm","-f", outFile), "") // need to remove outFile otherwise rustfilt will fail

    // Note that we don't add the option -h so hashes will be stripped.
    val (_,errorMsg,exitcode) = runCommand(listOf("rustfilt", "-i", inFile, "-o", outFile), "")
    if (exitcode != 0) {
        sbfLogger.warn {"rustfilt $errorMsg"}
        return null
    }
    // Process the output file
    val out = readLines(outFile)
    runCommand(listOf("rm","-f", inFile), "")
    runCommand(listOf("rm","-f", outFile), "")
    return out
}
