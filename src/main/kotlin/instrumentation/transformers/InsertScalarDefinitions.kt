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

package instrumentation.transformers

import datastructures.stdcollections.*
import analysis.maybeNarrow
import tac.Tag
import vc.data.*
import java.math.BigInteger

/* BG 20230113
 * Memory that has been scalarized needs to have the same "initialized to zero" semantics as the memory it is derived from.
 * Find all EVM_MEMORY_SCALARIZED variables that are havoc'd and make them initially zero instead.
 */

object InsertScalarDefinitions {
    fun transform(tacProgram: CoreTACProgram): CoreTACProgram {
        val patching = tacProgram.toPatchingProgram()

        tacProgram.analysisCache.graph.commands.mapNotNull {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignHavocCmd>()
                ?.takeIf { havocCmdLTACCmdView -> havocCmdLTACCmdView.cmd.lhs.tag == Tag.Bit256 }
        }.forEach { ltacHavocCmd ->
            val lhs = ltacHavocCmd.cmd.lhs
            if(lhs.tag is Tag.Bit256 && lhs.meta.containsKey(TACMeta.EVM_MEMORY_SCALARIZED)) {
                patching.replaceCommand(ltacHavocCmd.ptr,
                    listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(lhs, TACSymbol.Const(BigInteger.ZERO)))
                    )
            }
        }

        return patching.toCode(tacProgram)
    }
}
