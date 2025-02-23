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

package spec.cvlast

import spec.cvlast.transformer.CVLExpTransformer
import utils.CollectingResult
import utils.CollectingResult.Companion.lift
import utils.extend

open class SubstitutorExp(val substitutor: Map<String, CVLExp>) : CVLExpTransformer<Nothing> {
    val dontSub = mutableMapOf<String, Boolean>()

    override fun quant(exp: CVLExp.QuantifierExp): CollectingResult<CVLExp, Nothing> {
        return dontSub.extend(exp.qVarName, true) {
            super.quant(exp)
        }
    }

    override fun idLhs(idLhs: CVLLhs.Id): CollectingResult<CVLLhs.Id, Nothing> = (if (dontSub[idLhs.id] == true) {
        idLhs
    } else {
        substitutor[idLhs.id]?.toLhs() as CVLLhs.Id? ?: idLhs
    }).lift()

    override fun variable(exp: CVLExp.VariableExp): CollectingResult<CVLExp, Nothing> = (if (dontSub[exp.id] == true) {
        exp
    } else {
        substitutor[exp.id] ?: exp
    }).lift()

}
