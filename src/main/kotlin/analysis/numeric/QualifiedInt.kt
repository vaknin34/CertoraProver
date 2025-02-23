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
 * An abstract value (with self-type [I]) that has an numeric approximation of type [I] (via [WithIntApproximation])
 * and which has some set of qualifiers of type [Q] (via [WithQualifiers])
 */
interface QualifiedInt<I, T: IntApprox<T>, Q: Qualifier<*>> : WithIntApproximation<T>, WithQualifiers<Q, I>
