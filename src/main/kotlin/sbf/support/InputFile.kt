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
import java.io.IOException
import java.nio.file.Files
import java.nio.file.Paths

@Suppress("SwallowedException")
fun readLines(filename: String): ArrayList<String>? {
    val res = ArrayList<String>()
    try {
        val lines = Files.readAllLines(Paths.get(filename))
        for (line in lines) {
           res.add(line)
        }
    } catch (e: IOException) {
        sbfLogger.warn {"Some problem occurred while reading $filename"}
        return null
    }
    return res
}

