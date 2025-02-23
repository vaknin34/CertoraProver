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

package analysis.numeric

/**
 * An instance of [IntValueSemantics] that is agnostic to any state representation, i.e.,
 * the semantics definitely do not consult the state that produced values of type [I], which are assumed to be
 * [UIntApprox]
 *
 * [I] is the type of value abstraction, which contains an integer abstraction of type [T].
 */
abstract class StatelessUIntValueSemantics<I: WithUIntApproximation<T>, T: UIntApprox<T>> : IntValueSemantics<I, T, Any, Any>()
