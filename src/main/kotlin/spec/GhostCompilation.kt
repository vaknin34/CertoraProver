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

package spec

import spec.cvlast.CVLExp
import spec.cvlast.CVLType
import vc.data.ParametricInstantiation
import vc.data.TACMeta
import vc.data.TACSymbol

object GhostCompilation {
    fun <R> handleGhostApplication(
        cvlCompiler: CVLCompiler,
        exp: CVLExp.ApplyExp.Ghost,
        singleton: (TACSymbol.Var) -> ParametricInstantiation<R>,
        multiArg: (TACSymbol.Var, List<CVLExp>, List<CVLType.PureCVLType>) -> ParametricInstantiation<R>
    ) : ParametricInstantiation<R> {
        val ghostFun = cvlCompiler
            .tacSymbolTable
            .getUninterpretedFunction(exp.id, exp.args.size)
            ?: error("could not find ghost function ${exp.id} in symbolTable")

        val resultTag = if (exp.args.isEmpty()) {
            ghostFun.cvlResultType.toTag()
        } else {
            ghostFun.asTag
        }

        val sym = TACSymbol.Var(exp.id, resultTag)
            .withMeta(TACMeta.CVL_GHOST)
            .withMeta(TACMeta.CVL_DISPLAY_NAME, exp.id)
            .withMeta(TACMeta.CVL_VAR, true)
            .withMeta(TACMeta.CVL_TYPE, exp.getPureCVLType())

        return if (exp.args.isEmpty()) {
            singleton(sym)
        } else {
            multiArg(sym, exp.args, ghostFun.cvlParamTypes)
        }
    }
}
