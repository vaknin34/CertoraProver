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

import allocator.Allocator
import spec.cvlast.CVLExp
import spec.cvlast.transformer.CVLAstTransformer
import spec.cvlast.transformer.CVLCmdTransformer
import spec.cvlast.transformer.CVLExpTransformer
import utils.CollectingResult
import utils.CollectingResult.Companion.lift
import utils.CollectingResult.Companion.safeForce
import datastructures.stdcollections.*
import spec.CVLReservedVariables
import spec.isWildcard

/** replace all quantifier variables with fresh variable names. */
class QuantifierVarRenamer : CVLAstTransformer<Nothing>(CVLCmdTransformer(QuantifierRenamerImpl()))

/** Alpha-rename all quantifier variables to fresh variable names. Requires that there is no shadowing. */
private class QuantifierRenamerImpl private constructor(
    private val substitutions : Map<String,String>,
) : CVLExpTransformer<Nothing> {

    constructor() : this(emptyMap())

    /** @return a copy of `this` extended with [key] mapped to [value] */
    private fun extend(key : String, value : String) : QuantifierRenamerImpl
        = QuantifierRenamerImpl(substitutions.toMutableMap().apply {
            check(put(key, value).let { it == null || key.isWildcard() }) {
                "Duplicate variable detected; QuantifierVarRenamer requires that there is no shadowing.  " +
                "Ensure that [SingleVariableDefinitionChecker] has been run."
            }
        })

    override fun quant(exp: CVLExp.QuantifierExp): CollectingResult<CVLExp, Nothing> {
        val newVar = "${CVLReservedVariables.prefix}_${exp.originalName}_${Allocator.getFreshNumber()}"

        return exp.copy(
            param = if (exp.param.id.isWildcard()) { exp.param } else { exp.param.copy(id = newVar) },
            body  = extend(exp.qVarName, newVar).expr(exp.body).safeForce()
        ).lift()
    }

    override fun variable(exp: CVLExp.VariableExp): CollectingResult<CVLExp, Nothing>
        = exp.copy(id = substitutions[exp.id] ?: exp.id).lift()
}

