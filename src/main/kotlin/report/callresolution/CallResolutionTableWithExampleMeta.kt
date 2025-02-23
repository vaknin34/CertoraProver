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
import utils.mapToSet

/**
 * [CallResolutionTable] with basic information, and in addition, some info about
 * counter-examples, such as which entries are relevant to which counter-examples.
 */
class CallResolutionTableWithExampleMeta internal constructor(override val rows: Set<Row>) :
    CallResolutionTable<CallResolutionTableWithExampleMeta.Row> {

    companion object {
        val Empty = CallResolutionTableWithExampleMeta(emptySet())
    }

    data class Row(
        override val caller: String,
        override val callSite: CallSite?,
        override val callee: Callee,
        override val summary: String,
        override val resolutionComments: Map<String, String>,
        override val status: CallResolutionTableRow.Status,
        val rowId: Int
    ) : CallResolutionTableRow {
        override fun toBase() =
            CallResolutionTableBase.Row(caller, callSite, callee, summary, resolutionComments, status)
    }

    /**
     * Meta-data related to examples of a result.
     * Used to resolve which counter-examples an entry
     * in a CallResolution table is relevant to
     * (the underlined summary occurs in those counter-examples).
     */
    sealed class ExampleMeta {

        /**
         * Ids of summaries commands used to connect a counter-example to
         * a corresponding set of entries in the CallResolution table.
         */
        abstract val summariesIds: Set<Int>

        object None : ExampleMeta() {

            override val summariesIds: Set<Int>
                get() = emptySet()
        }

        data class Some(override val summariesIds: Set<Int>) : ExampleMeta() {
            init {
                require(summariesIds.isNotEmpty()) {
                    "[CallResolutionExampleMeta.Some] must have at least one summary id"
                }
            }
        }
    }

    override fun toCallResTableReporterView(exampleMeta: ExampleMeta): PerRuleCallResolutionReportView {
        return PerRuleCallResolutionReportView(
            rows.mapToSet {
                PerRuleCallResolutionReportView.RowView(
                    row = it.toBase(),
                    isInCounterExample = it.rowId in exampleMeta.summariesIds
                )
            }
        )
    }

    override fun copyAndFilterTable(isWarning: Boolean): CallResolutionTableWithExampleMeta {
        return CallResolutionTableWithExampleMeta(
            rows.filterTo(mutableSetOf()) {
                it.status.isWarning() == isWarning
            }
        )
    }


}
