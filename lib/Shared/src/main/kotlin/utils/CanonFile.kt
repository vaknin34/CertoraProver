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

package utils

import java.io.File
import java.nio.file.Path

/** a canonicalized file path, usable as a key in a map of files */
class CanonFile(file: File) {
    val canon: File = file.canonicalFile

    constructor(path: String) : this(File(path))

    constructor(path: Path) : this(path.toFile())

    fun exists() = canon.exists()

    override fun toString() = canon.toString()

    override fun hashCode() = canon.hashCode()

    override fun equals(other: Any?): Boolean = when {
        this === other -> true
        other !is CanonFile -> false
        else -> this.canon == other.canon
    }
}
