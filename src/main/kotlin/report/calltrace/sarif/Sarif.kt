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

package report.calltrace.sarif

import datastructures.NonEmptyList
import datastructures.stdcollections.*
import kotlinx.serialization.json.*
import report.TreeViewRepJsonObjectBuilder
import report.TreeViewReportable
import report.calltrace.CallTraceAttribute
import report.calltrace.altReprsInTreeView
import report.calltrace.formatter.CallTraceValueFormatter
import report.calltrace.printer.CallTracePrettyPrinter
import report.calltrace.sarif.SarifBuilder.Companion.mkSarif
import report.putJsonArray
import utils.*

/**
 * represents a SARIF-like format string, used in serialization of this class.
 * conceptually similar to a `printf` string.
 * placeholders in the format string are sequential (zero-based)
 * and use the syntax '{n}', where `n` corresponds to the n'th
 * argument in [args].
 *
 * for example, one such string could be: myFunc('{0}', '{1}') returns '{2}'
 */
data class Sarif internal constructor(val pieces: List<String>, val args: List<Arg>): TreeViewReportable {
    init {
        require(pieces.size == args.size + 1) {
            "got malformed input: pieces = $pieces, args = $args"
        }
    }

    /** constructs the format string represented by this instance of the class */
    override fun toString(): String {
        val message = StringBuilder()

        /**
         * since we assume `pieces.size == args.size + 1`,
         * and since [Iterable.zip] has the length of the
         * shorter iterator, there would be exactly one
         * piece remaining after this `for` loop.
         */
        for ((piece, idx) in pieces.zip(args.indices)) {
            message.append(piece)

            val ph = """'{$idx}'"""
            message.append(ph)
        }

        // ...and now we add the remaining piece
        message.append(pieces.last())

        return message.toString()
    }


    /** Flatten back to string -- fill in the first element of `values` for each [Arg]. This is the representation
     * that works for our textual regressions, too.
     * (if we ever change default order and textual regressions fail because of it, we might pick a different
     * representation for flattening here)
     * */
    fun flatten(): String {
        val message = StringBuilder()
        for ((piece, idx) in pieces.zip(args.indices)) {
            message.append(piece)
            val ph = args[idx].values.head
            message.append(ph)
        }
        message.append(pieces.last())
        return message.toString()
    }

    /** If this is just an [Sarif.Arg.asSarif], return the [Arg], else null. (not extremely elegant, but at
     * places, it seems) */
    fun asArg() =
        runIf(pieces.size == 2 && args.size == 1 && pieces.all { it.isEmpty() }) {
            args.first()
        }

    fun asArgOrUnknown() = asArg() ?: CallTraceValueFormatter.unknownArg()

    /** Analogous logic to [toString], for use in [CallTracePrettyPrinter] */
    fun prettyPrint(): String {
        val message = StringBuilder()
        for ((piece, idx) in pieces.zip(args.indices)) {
            message.append(piece)
            val ph = args[idx].let { "${it.values.head}:${it.type}"}
            message.append(ph)
        }
        message.append(pieces.last())
        return message.toString()
    }

    override val treeViewRepBuilder get() = TreeViewRepJsonObjectBuilder {
        put(CallTraceAttribute.TEXT(), this@Sarif.toString())
        putJsonArray(CallTraceAttribute.ARGUMENTS(), args)
    }

    data class Arg(
        val values: NonEmptyList<String>,
        val tooltip: String?,
        val type: String?,
    ) : TreeViewReportable {

        override val treeViewRepBuilder get() = TreeViewRepJsonObjectBuilder {
            val arg = this@Arg
            if (values.isNotEmpty()) {
                put(CallTraceAttribute.VALUE(), arg.values.first()) // legacy, for backwards compatibility
            }
            if (altReprsInTreeView) {
                put(
                    CallTraceAttribute.VALUES(),
                    buildJsonArray { arg.values.forEach { add(it) } }
                )
            }
            arg.tooltip?.let { put(CallTraceAttribute.TOOLTIP(), it) }
            // arg.type?.let { put(CallTraceAttribute.TYPE(), it) } // not printing them for now -- bring them back if/when they're used
        }

        /** A [Sarif] containing this [Arg] surrounded by two empty strings. */
        val asSarif get() = mkSarif { append(this@Arg) }
    }

    companion object {
        /**
         * constructs a [Sarif] without args or placeholders.
         * NOTE: caller asserts that [str] contains no placeholders.
         */
        fun fromPlainStringUnchecked(str: String): Sarif = Sarif(pieces = listOf(str), args = emptyList())

        /** the string used to the separate an expression from its value */
        const val EVALUATES_TO: String = " ↪ "
    }
}
