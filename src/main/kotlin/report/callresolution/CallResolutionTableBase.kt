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

import utils.mapToSet
import report.callresolution.CallResolutionTableWithExampleMeta.ExampleMeta
import datastructures.stdcollections.*

/**
 * A [CallResolutionTable] with basic information only (no info related to
 * counter-examples).
 */
class CallResolutionTableBase internal constructor(override val rows: Set<Row>) :
    CallResolutionTable<CallResolutionTableBase.Row> {

    data class Row(
        override val caller: String,
        override val callSite: CallSite?,
        override val callee: Callee,
        override val summary: String,
        override val resolutionComments: Map<String, String>,
        override val status: CallResolutionTableRow.Status
    ) : CallResolutionTableRow {
        override fun toBase(): Row = this
    }

    companion object {
        val Empty = CallResolutionTableBase(emptySet())
    }

    /**
     * A builder for [CallResolutionTableBase] which is mutable, in the sense
     * of having the ability to append new rows.
     * When no more entries are expected to be appended, can be converted to an
     * immutable version using the [toTable] method.
     */
    class Builder {
        private val coreRows: MutableSet<Row> = mutableSetOf()

        private fun addRow(row: CallResolutionTableRow): Builder = apply {
            coreRows.add(row.toBase())
        }

        /**
         * Appends all the rows from [table] to this table-builder.
         */
        fun joinWith(table: CallResolutionTable<*>): Builder = apply {
            table.rows.forEach(::addRow)
        }

        fun toTable(): CallResolutionTableBase = CallResolutionTableBase(coreRows.toSet())
    }

    override fun toCallResTableReporterView(exampleMeta: ExampleMeta): PerRuleCallResolutionReportView {
        return PerRuleCallResolutionReportView(
            rows.mapToSet {
                PerRuleCallResolutionReportView.RowView(
                    row = it,
                    isInCounterExample = false
                )
            }
        )
    }

    override fun copyAndFilterTable(isWarning: Boolean): CallResolutionTableBase {
        return CallResolutionTableBase(
            rows.filterTo(mutableSetOf()) {
                it.status.isWarning() == isWarning
            }
        )
    }
}
