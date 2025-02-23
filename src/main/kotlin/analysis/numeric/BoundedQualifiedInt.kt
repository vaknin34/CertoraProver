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

import java.math.BigInteger

/**
 * An interface describing a [QualifiedInt] that can be updaed with bounds and qualifiers
 * via [withBoundAndQualifiers].
 *
 * [I] is the self type, and implementers are expected to use the static name of the implementation
 * as the value of [I].
 *
 * [Q] is the type of qualifiers, and [U] is the [UIntApprox] instance used by this value
 */
interface BoundedQualifiedInt<I, Q: Qualifier<Q>, U: IntApprox<U>> : QualifiedInt<I, U, Q> {
    fun withBoundAndQualifiers(lb: BigInteger, ub: BigInteger, quals: Iterable<Q>): I
}
