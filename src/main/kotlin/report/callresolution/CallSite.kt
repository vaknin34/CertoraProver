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

package report.callresolution

import com.certora.collect.*
import compiler.SourceSegment
import kotlinx.serialization.json.put
import report.*

/**
 * Call-site from the source of a CallCore command.
 */
@Treapable
data class CallSite(val sourceSegment: SourceSegment): TreeViewReportable {

    val srcSnippet: String get() = sourceSegment.sanitizedContent
    val loc: TreeViewLocation get() = sourceSegment

    private enum class TreeViewAttribute(private val repString: String) {
        SNIPPET("snippet"),
        JUMP_TO_DEFINITION("jumpToDefinition");

        operator fun invoke(): String = repString
    }

    override val treeViewRepBuilder: TreeViewRepBuilder<*> = TreeViewRepJsonObjectBuilder {
        put(TreeViewAttribute.SNIPPET(), srcSnippet)
        put(TreeViewAttribute.JUMP_TO_DEFINITION(), loc)
    }
}
