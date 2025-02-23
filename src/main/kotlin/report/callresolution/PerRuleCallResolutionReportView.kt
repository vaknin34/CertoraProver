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

import kotlinx.serialization.json.put
import report.TreeViewRepJsonObjectBuilder
import report.put

/**
 * A view of a CallResolution table which is associated with a specific rule.
 */
class PerRuleCallResolutionReportView(override val rowViews: Set<RowView>) :
    CallResolutionTableReportView<PerRuleCallResolutionReportView.RowView>() {

    data class RowView(
        override val row: CallResolutionTableBase.Row,
        val isInCounterExample: Boolean
    ) : CallResolutionTableRowReportView<CallResolutionTableBase.Row>() {

        override val treeViewRepBuilder = TreeViewRepJsonObjectBuilder {
            super.treeViewRepBuilder coalesceInto this
            put(Attribute.CALLEE(), row.callee)
            put(Attribute.IS_IN_COUNTER_EXAMPLE(), isInCounterExample)
        }
    }

}
