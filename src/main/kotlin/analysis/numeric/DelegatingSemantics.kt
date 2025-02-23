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
 * An implementation of of [IValueSemantics] that by default delegates to [delegate].
 * i.e., all "super" calls in overriders will delegate to the implementation in [delegate]
 */
open class DelegatingSemantics<in S, I, in W>(private val delegate: IValueSemantics<S, I, W>) : IValueSemantics<S, I, W> by delegate