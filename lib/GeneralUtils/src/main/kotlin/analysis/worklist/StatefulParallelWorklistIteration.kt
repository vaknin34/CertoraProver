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

package analysis.worklist

sealed class ParallelStepResult<out T, out U, out R> {
    data class StopWith<R>(val r: R) : ParallelStepResult<Nothing, Nothing, R>()
    data class FullResult<T, U>(val cont: List<T>, val res: List<U>) : ParallelStepResult<T, U, Nothing>()
    data class ContinueWith<T>(val cont: List<T>) : ParallelStepResult<T, Nothing, Nothing>()
    data class Result<U>(val res: List<U>) : ParallelStepResult<Nothing, U, Nothing>()
}

