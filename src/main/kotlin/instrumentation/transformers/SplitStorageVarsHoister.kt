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

import instrumentation.StoragePathAnnotation
import tac.MetaMap
import vc.data.*
import vc.data.TACMeta.STORAGE_KEY

/**
 * Split storage variables may end up inside expressions, which creates bugs in applying hooks
 */
object SplitStorageVarsHoister {
    // gets all split storage reads from the command's rhs
    private fun getSplitStorageReads(cmd: TACCmd.Simple) =
        cmd.getFreeVarsOfRhs().filter { it.meta.containsKey(STORAGE_KEY) && it.tag.isPrimitive() }

    // a command with non empty set of storage reads, but not an assign command of the symbol alone
    private fun cmdWithStorageReads(cmd: TACCmd.Simple) =
        (cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd || cmd.rhs !is TACExpr.Sym.Var) && getSplitStorageReads(cmd).isNotEmpty()

    private fun cmdTransformer(readsToReplacements: Map<TACSymbol.Var, TACSymbol.Var>) =
        object : DefaultTACCmdMapper() {
            override fun mapVar(t: TACSymbol.Var): TACSymbol.Var =
                readsToReplacements.getOrDefault(t, t)


            // don't replace lhs-s
            override fun mapLhs(t: TACSymbol.Var): TACSymbol.Var = t
        }

    fun transform(code: CoreTACProgram): CoreTACProgram {
        val p = code.toPatchingProgram()
        val g = code.analysisCache.graph
        g.commands.filter { cmdWithStorageReads(it.cmd) }
            .map { lcmd ->
                val reads = getSplitStorageReads(lcmd.cmd)
                val readsToReplacements =
                    reads.associateWith { TACKeyword.TMP(it.tag, "replacement").toUnique().also { p.addVarDecl(it) } }


                val new = readsToReplacements.map { (read, replacement) ->
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        replacement,
                        read,
                        meta = MetaMap(TACMeta.STORAGE_PRINTER to StoragePathAnnotation.StoragePathPrinter)
                    )
                } + cmdTransformer(readsToReplacements).map(lcmd.cmd)

                p.replaceCommand(
                    lcmd.ptr,
                    new
                )
            }

        return p.toCode(code)
    }
}