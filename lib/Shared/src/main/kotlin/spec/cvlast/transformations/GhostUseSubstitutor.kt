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

package spec.cvlast.transformations

import spec.cvlast.CVLExp
import spec.cvlast.transformer.CVLExpTransformer
import utils.CollectingResult
import utils.CollectingResult.Companion.bind
import utils.CollectingResult.Companion.map


class GhostUseSubstitutor<T>(
    val ghostAppSubstitutor: (CVLExp.ApplyExp.Ghost) -> CollectingResult<CVLExp?, T>,
    val arrayDerefSubstitutor: (CVLExp.ArrayDerefExp) -> CollectingResult<CVLExp?, T>
) : CVLExpTransformer<T> {
    override fun ghost(exp: CVLExp.ApplyExp.Ghost): CollectingResult<CVLExp.ApplyExp.Ghost, T> =
        ghostAppSubstitutor(exp).map { e -> e as? CVLExp.ApplyExp.Ghost ?: exp }.bind { super.ghost(it) }

    override fun arrayderef(exp: CVLExp.ArrayDerefExp): CollectingResult<CVLExp.ArrayDerefExp, T> =
        arrayDerefSubstitutor(exp).map { e -> e as? CVLExp.ArrayDerefExp ?: exp }

}
