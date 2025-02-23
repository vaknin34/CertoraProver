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

import report.calltrace.formatter.CallTraceValueFormatter
import report.calltrace.formatter.FormatterType
import utils.*
import vc.data.state.TACValue
import kotlin.collections.single
import datastructures.stdcollections.*
import report.calltrace.formatter.CallTraceValueFormatter.Companion.unknown
import report.calltrace.formatter.CallTraceValue
import report.calltrace.sarif.SarifBuilder.Companion.mkSarif
import spec.cvlast.CVLType
import spec.cvlast.typedescriptors.EVMTypeDescriptor
import spec.cvlast.typedescriptors.VMTypeDescriptor

/** allows incrementally building a [Sarif], while maintaining that class's invariants */
class SarifBuilder {
    private val pieces: MutableList<String> = mutableListOf("")
    private val args: MutableList<Sarif.Arg> = mutableListOf()

    fun append(str: String) {
        val last = this.removeLastPiece()
        this.pieces.add(last + str)
    }

    fun append(arg: Sarif.Arg) {
        // empty strings mark the location of an argument,
        // so that parsing can be implemented as a simple interlace operation
        pieces.add("")
        args.add(arg)
    }

    fun removeSuffix(suffix: String) {
        val last = this.removeLastPiece()
        this.pieces.add(last.removeSuffix(suffix))
    }

    private fun removeLastPiece(): String {
        return this.pieces.removeLastOrNull() ?: error("broken invariant: pieces can't be empty")
    }

    fun append(other: Sarif) {
        val otherPiecesIter = other.pieces.listIterator()
        val firstPiece = otherPiecesIter.nextOrNull() ?: return // should be non-empty, but no throwing here

        // first piece should be concatenated
        this.append(firstPiece)

        // ...but the rest can just be appended
        for (piece in otherPiecesIter) {
            this.pieces.add(piece)
        }

        // since we're concatenating the other sarif at the end, we can just add the args
        this.args.addAll(other.args)
    }


    fun build(): Sarif {
        // if the last push was an arg, then the list of pieces
        // was terminated by an empty string.
        // otherwise args is empty and pieces contains just the empty string,
        // since that's what we initialized it as
        return Sarif(this.pieces, this.args)
    }

    companion object {
        fun mkSarif(actions: SarifBuilder.() -> Unit) = SarifBuilder().apply { actions() }.build()

        fun <T> Iterable<T>.joinToSarif(
            separator: String = " ",
            prefix: String = "",
            postfix: String = "",
            action: (Int, T) -> Sarif,
        ): Sarif = mkSarif {
            append(prefix)
            val iterator = this@joinToSarif.iterator()
            var ctr = 0;
            while (iterator.hasNext()) {
                append(action(ctr, iterator.next()))
                if (iterator.hasNext()) {
                    append(separator)
                }
                ctr++
            }
            append(postfix)
        }
    }
}

class SarifFormatter(val ctf: CallTraceValueFormatter) {

    /**
     * takes a string, [template], with "{}" as placeholders,
     * plus a list of [FmtArg] to be inserted at those locations.
     * this behaves similar to "printf".
     * (currently deals with logic errors by throwing. please test your input accordingly)
     */
    fun fmt(template: String, vararg fmtArgs: FmtArg): Sarif {
        val builder = SarifBuilder()

        @Suppress("ForbiddenMethodCall")
        val split = template.split("{}")

        require(split.size - 1 == fmtArgs.size) {
            "mismatch between arg list size and number of placeholders in template"
        }

        when (split.size) {
            0 -> `impossible!` // from `split` impl
            1 -> builder.append(split.single())
            else -> {
                /**
                 * note that the pieces list is non-empty,
                 * and that we assume `pieces.size == args.size + 1`
                 *
                 * see [Sarif.toString] for rationale behind
                 * splitting this into a `zip` + `last`
                 */
                for ((piece, fmtArg) in split.zip(fmtArgs)) {
                    builder.append(piece)

                    when (fmtArg) {
                        is FmtArg.CtfValue -> {
                            val arg = fmtArg.toArg(ctf)
                            builder.append(arg)
                        }
                        is FmtArg.InlineSarif -> builder.append(fmtArg.sarif)
                        is FmtArg.Str -> builder.append(fmtArg.str)
                        FmtArg.To -> builder.append(Sarif.EVALUATES_TO)
                    }
                }

                // ...and now we add the remaining piece
                builder.append(split.last())
            }
        }

        return builder.build()
    }
}

/** arguments that can be used in [SarifFormatter.fmt] */
sealed interface FmtArg {
    /**
     * we plan to eventually migrate all this formatter logic we leaked here,
     * to the formatter itself, by having the formatter output [Sarif].
     */
    data class CtfValue(
        val ctfValue: CallTraceValue,
        val tooltip: String = "value",
    ) : FmtArg {
        companion object {
            fun buildOrUnknown(tv: TACValue?, type: EVMTypeDescriptor, tooltip: String = "value") =
                tv?.let {
                    CtfValue(CallTraceValue.EVMType(tv, type), tooltip)
                } ?: InlineSarif(unknown())
            fun buildOrUnknown(tv: TACValue?, type: VMTypeDescriptor?, tooltip: String = "value") =
                tv?.let {
                    type?.let {
                        CtfValue(CallTraceValue.VMType(tv, type), tooltip)
                    } ?: CtfValue(CallTraceValue.UnknownType(tv, "unknown vmTypeDescriptor"), tooltip)
                } ?: InlineSarif(unknown())
            fun buildOrUnknown(tv: TACValue?, type: CVLType.PureCVLType, tooltip: String = "value") =
                tv?.let {
                    CtfValue(CallTraceValue.CVLType(tv, type), tooltip)
                } ?: InlineSarif(unknown())
        }
        val type: FormatterType<*> get() = ctfValue.formatterType

        fun toArg(formatter: CallTraceValueFormatter): Sarif =
            mkSarif {
                ctfValue.paramName?.let { append(it) }
                append(ctfValue.toSarif(formatter, tooltip))
            }
    }

    /** an inline [Sarif] to splat into the format string */
    @JvmInline
    value class InlineSarif(val sarif: Sarif) : FmtArg

    /**
     * a string to splat into the format string.
     *
     * you can simply use Kotlin's built-in string formatting instead of using this,
     * however this is useful to mark things that are currently strings,
     * but should eventually be changed to something more useful, like a [Sarif].
     * that way the format string itself doesn't require significant changes.
     */
    @JvmInline
    value class Str(val str: String) : FmtArg

    /** a shorthand for an explicit [Sarif.EVALUATES_TO] */
    data object To : FmtArg
}

// convenience functions

fun FmtArg(sarif: Sarif) = FmtArg.InlineSarif(sarif)
fun FmtArg(str: String) = FmtArg.Str(str)
