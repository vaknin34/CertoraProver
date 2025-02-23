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

/**
 * A [TACFile] represents a dumped [TAC] program on disk.
 * A [parseableFile] is the path to the file that can be re-parsed by the tool for debugging it.
 * A [graphFile] is the HTML representation for looking at it.
 */
data class TACFile(
    val name: String,
    val parseableFile: String,
    val isBinary: Boolean,
    val graphFile: String? = null
)