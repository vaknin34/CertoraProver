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

import datastructures.stdcollections.*
import kotlinx.serialization.json.addJsonObject
import kotlinx.serialization.json.put
import report.*
import report.callresolution.GlobalCallResolutionReportView.RowView.Companion.asGlobalView
import utils.mapToSet

/**
 * A view of a global CallResolution table for all the function calls from all the rules.
 * Each call is described in terms of a caller that calls to a callee.
 * The tab has a list of callee functions, where each callee element is structured as follows:
 * [callee function signature]: For each caller, present the following data ([RowView]):
 *   Caller signature.
 *   Call-site from the source code.
 *   Havoc type.
 *   Rule identifier (i.e., the name of the rule where the call occurs).
 *   Indication for whether the call was successfully resolved by the tool.
 */
class GlobalCallResolutionReportView private constructor(override val rowViews: Set<RowView>) :
    CallResolutionTableReportView<GlobalCallResolutionReportView.RowView>() {

    private val calleesToGlobalRowsViews: Map<Callee, List<RowView>> = rowViews.groupBy { it.row.callee }

    /**
     * A view of an entry in the global CallResolution table.
     */
    data class RowView(
        override val row: CallResolutionTableBase.Row
    ) : CallResolutionTableRowReportView<CallResolutionTableBase.Row>() {

        companion object {
            fun CallResolutionTableBase.Row.asGlobalView() = RowView(this)
        }

        override val treeViewRepBuilder = TreeViewRepJsonObjectBuilder {
            super.treeViewRepBuilder.builderAction(this)
            put(Attribute.IS_WARNING(), row.status.isWarning())
        }
    }

    override val treeViewRepBuilder = TreeViewRepJsonArrayBuilder {
        calleesToGlobalRowsViews.forEachEntry { (callee, callResRows) ->
            addJsonObject {
                put(Attribute.CALLEE(), callee)
                putJsonArray(Attribute.GLOBAL_CALL_RESOLUTION_ROWS(), callResRows)
            }
        }
    }

    /**
     * A builder for a global [CallResolutionTable]'s view which is mutable, in the sense
     * of having the ability to append new rows.
     * When no more entries are expected to be appended, can be converted to an
     * immutable version using the [toGlobalReportView] method.
     */
    class Builder {

        private val globalRowViews: MutableSet<RowView> = mutableSetOf()

        private fun addRowView(globalRowView: RowView) {
            synchronized(this) {
                globalRowViews.add(globalRowView)
            }
        }

        fun joinWith(table: CallResolutionTable<*>): Builder = apply {
            table.rows.forEach { addRowView(it.toBase().asGlobalView()) }
        }

        fun toGlobalReportView(): GlobalCallResolutionReportView {
            return GlobalCallResolutionReportView(
                synchronized(this) {
                    globalRowViews.mapToSet { it }
                }
            )
        }
    }
}
