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

package rules.dpgraph


/**
 * Wrapper for the unreduced result of the computation done by [DPGraph] that holds additional info about the
 * computation. Each result is of one of two feasible types, one that indicates a good result and one that indicate a
 * bad one.
 * @property computationalTyp tells if the result is obtained by the task execution or by conclusion from predecessors.
 * @param R type of the result
 * @param S subtype of [R] indicating a good result (success)
 * @param E subtype of [R] indicating a bad result (error)
 */
sealed interface DPResult<out R, out S: R, out E: R> {

    enum class ComputationalType(private val uiString: String?) {
        CONCLUDED("Prover concluded the final result from other checks"),
        COMPUTED(null),
        ;
        fun toUIStringOrNull(): String? = uiString
    }

    val result: R
    val computationalTyp: ComputationalType

    companion object {
        inline operator fun <R, reified S: R, reified E: R> invoke(
            result: R, computationalTyp: ComputationalType
        ): DPResult<R, S, E> =
            when (result) {
                is E -> Error(result, computationalTyp)
                is S -> Success(result, computationalTyp)
                else -> throw IllegalArgumentException("Expected result type to be S or E")
            }
    }

    data class Success<out R, out S: R>(
        override val result: S,
        override val computationalTyp: ComputationalType
    ) : DPResult<R, S, Nothing>

    data class Error<out R, out E: R>(
        override val result: E,
        override val computationalTyp: ComputationalType
    ) : DPResult<R, Nothing, E>
}
