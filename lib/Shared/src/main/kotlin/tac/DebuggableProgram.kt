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

package tac

import config.OUTPUT_NAME_DELIMITER

/**
 * [DumpType] is an artifact's descriptor.
 * Today, for programs, this refers to the transformation last applied on it.
 * Debug flags impact which [DumpType]s are actually going to be dumped as determined by [isEnabled()].
 */
interface DumpType {
    fun isEnabled(): Boolean
}

enum class DumpTime(private val reportSuffix: String) {
    PRE_TRANSFORM("pre"),
    POST_TRANSFORM("post"),
    AGNOSTIC("") {
        override val reportSuffixWithDelimiter: String
            get() = ""
    },
    ;
    open val reportSuffixWithDelimiter: String
        get() = "$reportSuffix$OUTPUT_NAME_DELIMITER"

}

/**
 * A [DebuggableProgram] describes an object that sometimes we need to dump for debugging purposes.
 * It is parametrized by the descriptor type. A default descriptor is provided in [defaultType].
 * The [dump] method receives a descriptor [dumpType] and a path [where] to store the artifacts.
 */
interface DebuggableProgram<T: DumpType> {
    fun dump(dumpType: T, where: String, time: DumpTime)
    fun dumpBinary(where: String, label: String): TACFile
    val defaultType: T
}
