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

import datastructures.stdcollections.*
import kotlinx.serialization.json.JsonPrimitive
import log.*
import report.TreeViewReportAttribute.*

private val logger = Logger(LoggerTypes.TREEVIEW_REPORTER)

/**
 * Generic format for reporting "live" information on an ongoing check of a single "rule" (the kind that corresponds to
 * a single [TACProgram] entering [TACVerifer]).
 *
 * see [annotateUIds] for explanation of [uId] numbering.
 */
class LiveCheckInfoNode private constructor(
    var uId: Int?,
    val label: String,
    val value: String?,
    val children: List<LiveCheckInfoNode>,
    val jumpToDefinition: TreeViewLocation? = TreeViewLocation.Empty,
    val severity: Int,
    val hSev: Int, // stands for "heuristical severity"
    val link: String? = null,
) : TreeViewReportable {

    override val treeViewRepBuilder: TreeViewRepBuilder<*>
        get() {
            check(uId != null) { "uId must have been initialized at this point" }
            return TreeViewRepJsonObjectBuilder(caching) {
                put(UI_ID(), JsonPrimitive(uId))
                put(LABEL(), JsonPrimitive(label))
                put(VALUE(), JsonPrimitive(value))
                put(
                    CHILDREN(),
                    TreeViewRepJsonArrayBuilder(caching) { addAll(children) }.build()
                )
                @Suppress("SwallowedException")
                try {
                    put(JUMP_TO_DEFINITION(), jumpToDefinition)
                } catch (e: IllegalStateException) {
                    logger.debug { "got exception when trying to serialize 'jumpToDefinition' object \"$jumpToDefinition\"" }
                    // do nothing, just omit the jumpToDef
                }
                put(SEVERITY(), JsonPrimitive(severity))
                put(HSEV(), JsonPrimitive(hSev))
                if (link != null) {
                    put(LINK(), JsonPrimitive(link))
                }
            }
        }
    companion object {
        private const val caching = true

        /** Create a [LiveCheckInfoNode] that only has a label, no children, no value. */
        fun onlyLabel(label: String) =
            LiveCheckInfoNode(
                uId = null,
                label = label,
                value = null,
                children = emptyList(),
                jumpToDefinition = TreeViewLocation.Empty,
                severity = 0,
                hSev = 0,
            )

        /** Create a [LiveCheckInfoNode] that has a label ("key") and a value, no children. */
        fun keyValue(
            label: String,
            value: String,
            jumpToDefinition: TreeViewLocation? = TreeViewLocation.Empty,
            severity: Int = 0,
            hSev: Int = 0,
            link: String? = null,
        ) =
            LiveCheckInfoNode(
                uId = null,
                label = label,
                value = value,
                children = emptyList(),
                jumpToDefinition = jumpToDefinition,
                severity = severity,
                hSev = hSev,
                link = link,
            )

        /** Create a [LiveCheckInfoNode] that has (or might have) children (will be unfoldable in the report if
         * `children` is non-empty). */
        fun many(
            label: String,
            children: List<LiveCheckInfoNode>,
            jumpToDefinition: TreeViewLocation? = TreeViewLocation.Empty,
            severity: Int = 0,
            hSev: Int = 0,
        ) =
            LiveCheckInfoNode(
                uId = null,
                label = label,
                value = null,
                children = children,
                jumpToDefinition = jumpToDefinition,
                severity = severity,
                hSev = hSev,
            )
    }
}
