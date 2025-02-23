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

import analysis.maybeNarrow
import config.Config
import tac.Tag
import vc.data.*
import vc.data.tacexprutil.TACExprFactSimple

/**
 * Replaces initial (freshly havocced) versions of certain maps (memory, codedata) with [MapDefinition]s that describe
 * their initial state (e.g. all 0s in the case of memory).
 */
object InsertMapDefinitions {
    fun transform(tacProgram: CoreTACProgram): CoreTACProgram {
        val patching = tacProgram.toPatchingProgram()

        // Hack: the metas of the havoc lhss aren't updated, it seems .. thus looking in the appearances of the symbol
        // in rhss
        val mapToBound = mutableMapOf<TACSymbol.Var, ImmutableBound>()
        tacProgram.analysisCache.graph.commands.forEach { ltacCmd ->
            ltacCmd.cmd.getFreeVarsOfRhs().forEach { mapVar ->
                if (mapVar.tag is Tag.ByteMap &&
                    mapVar.meta.find(TACMeta.EVM_IMMUTABLE_ARRAY) != null
                ) {
                    val bound: ImmutableBound = mapVar.meta.find(TACMeta.EVM_IMMUTABLE_ARRAY)!!
                    check(!mapToBound.containsKey(mapVar) || mapToBound[mapVar] == bound)
                    {
                        "In ${tacProgram.name}: two occurrences of the same variable (in right hand sides) have a different meta annotation:" +
                                "$mapVar is annotated with ${mapToBound[mapVar]} as well as $bound"
                    }
                    mapToBound[mapVar] = bound
                }
            }
        }

        tacProgram.analysisCache.graph.commands
            .mapNotNull {
                it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignHavocCmd>()
                    ?.takeIf { havocCmdLTACCmdView -> havocCmdLTACCmdView.cmd.lhs.tag == Tag.ByteMap }
            }
            .forEach { ltacHavocCmd ->
                val mapVar = ltacHavocCmd.cmd.lhs
                val mapDef = if (mapVar.tag is Tag.ByteMap && mapVar.meta.containsKey(TACMeta.EVM_MEMORY)) {
                    if (!Config.HavocInitEVMMemory.get()) {
                        TACExprFactUntyped.resetStore(mapVar.tag as Tag.Map)
                    } else {
                        null
                    }
                } else if (mapVar.tag is Tag.ByteMap &&
                    mapVar.meta.find(TACMeta.EVM_IMMUTABLE_ARRAY) != null
                ) {
                    val bound: ImmutableBound = mapToBound[mapVar]
                        ?: mapVar.meta.find(TACMeta.EVM_IMMUTABLE_ARRAY) // uh, so hacky.. e.g. Test/StructPacking/DynamicStruct needs this line though
                        ?: error("failed to lookup bound of EVM_IMMUTABLE_ARRAY $mapVar")
                    if (bound.sym is TACSymbol.Var && !tacProgram.symbolTable.contains(bound.sym)) {
                        // it's unclear to me why I need to do this; the symbol seems to be mentioned nowhere else ..
                        //  - should there be a havoc for it? -- should I insert one? (under some conditions?)
                        patching.addVarDecl(bound.sym)
                    }
                    val i = TACSymbol.Factory.getFreshAuxVar(
                        TACSymbol.Factory.AuxVarPurpose.MAP_DEF_INSERTER,
                        TACSymbol.Var("i", Tag.Bit256)
                    ).asSym()
                    TACExpr.MapDefinition(
                        listOf(i),
                        TACExprFactSimple {
                            ite(i lt bound.sym.asSym(), unconstrained(Tag.Bit256), number(0))
                        },
                        Tag.ByteMap
                    )
                } else {
                    null
                }
                if (mapDef != null) {
                    val newCmd = TACCmd.Simple.AssigningCmd.AssignExpCmd(mapVar, mapDef)
                    patching.replaceCommand(ltacHavocCmd.ptr, listOf(newCmd))
                }
            }
        return patching.toCode(tacProgram)
    }
}
