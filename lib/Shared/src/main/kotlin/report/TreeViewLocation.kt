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

package report

import kotlinx.serialization.json.JsonObjectBuilder
import kotlinx.serialization.json.put
import utils.SourcePosition
import java.io.File

/**
 * Represents the value of a "jump to definition" attribute in a treeView report
 * A location in a resource (e.g., sol or spec files) that can be reported in a treeView report
 */
interface TreeViewLocation : TreeViewReportable {
    /** The (relative) path of the resource */
    val file: String

    /** 0-based position in the file where the resource begins */
    val start: SourcePosition

    /** 0-based position in the file where the resource ends */
    val end: SourcePosition

    /** 1-based line number of where this resource begins */
    val lineNumber get() = start.lineForIDE

    /** 0-based line number of where this resource begins */
    val lineNumberZeroBased get() = start.line.toInt()

    val fileName: String get() = File(file).name

    override val treeViewRepBuilder: TreeViewRepBuilder<JsonObjectBuilder>
        get() = TreeViewRepJsonObjectBuilder {
            put(key = "file", value = file)
            put(key = "start", element = start.toJsonObject())
            put(key = "end", element = end.toJsonObject())
        }

    companion object {
        val Empty : TreeViewLocation? = null
    }

}
