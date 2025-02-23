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

package normalizer

import analysis.maybeNarrow
import tac.MetaKey
import utils.mapNotNull
import utils.`to?`
import vc.data.CoreTACProgram
import vc.data.SimplePatchingProgram.Companion.patchForEach
import vc.data.TACBuiltInFunction
import vc.data.TACCmd
import vc.data.TACExpr
import datastructures.stdcollections.*

/**
 * Removes desired annotations from a TAC program.
 */
object AnnotationRemover {
    fun removeAnnotations(
        c: CoreTACProgram,
        filter: (TACCmd.Simple.AnnotationCmd) -> Boolean
    ): CoreTACProgram {
        return c.parallelLtacStream().filter {
            it.cmd is TACCmd.Simple.AnnotationCmd && filter(it.cmd)
        }.patchForEach(c) {
            this.replaceCommand(it.ptr, listOf(TACCmd.Simple.NopCmd))
        }
    }

    fun removeAnnotations(
        c: CoreTACProgram,
        annotationsToRemove: List<MetaKey<*>>
    ): CoreTACProgram {
        return removeAnnotations(c) { it.annot.k in annotationsToRemove }
    }

    fun removeOpaqueIdentities(c: CoreTACProgram): CoreTACProgram {
        return c.parallelLtacStream().mapNotNull {
            it.ptr `to?` it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.let { exp ->
                exp.cmd.rhs as? TACExpr.Apply
            }?.takeIf { app ->
                app.f is TACExpr.TACFunctionSym.BuiltIn && (app.f as TACExpr.TACFunctionSym.BuiltIn).bif is TACBuiltInFunction.OpaqueIdentity &&
                    app.ops.size == 1
            }?.ops?.single()
        }.patchForEach(c) { (where, op) ->
            this.update(where) { cmd ->
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = cmd.getLhs()!!,
                    rhs = op,
                    meta = cmd.meta
                )
            }
        }
    }
}
