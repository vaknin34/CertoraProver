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

package icfg

import analysis.icfg.CallGraphBuilder
import analysis.storage.DisplayPath
import analysis.storage.StorageAnalysis
import datastructures.stdcollections.*
import evm.EVM_WORD_SIZE
import log.Logger
import log.LoggerTypes
import scene.IContractWithSource
import scene.TACMethod
import utils.*
import vc.data.*
import java.util.stream.Collectors

private val logger = Logger(LoggerTypes.INLINER)

/**
 * Resolves struct slot references to contracts instances ids where possible
 */
object ContractStorageResolver {
    fun resolve(m: TACMethod) : CoreTACProgram {
        val prog = m.code as CoreTACProgram
        val src = (m.getContainingContract() as? IContractWithSource)?.src ?: return prog
        if(src.structLinkingInfo.isEmpty() && src.legacyStructLinking.isEmpty()) {
            return prog
        }
        val resolutions = prog.parallelLtacStream().filter {
            (it.cmd is TACCmd.Simple.AssigningCmd.WordLoad && it.cmd.meta.containsKey(TACMeta.IS_STORAGE_ACCESS))
                    || (it.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && it.cmd.rhs is TACExpr.Sym.Var &&
                    it.cmd.rhs.s.meta.find(TACMeta.STORAGE_KEY) != null)
        }.filter {
            it.cmd.meta.find(CallGraphBuilder.ContractStorageRead.META_KEY) != null
        }.mapNotNull {
            val (contractInstanceId, display, path) = when(it.cmd) {
                is TACCmd.Simple.AssigningCmd.WordLoad -> {
                    Triple(
                        it.cmd.base.meta.find(TACMeta.STORAGE_KEY),
                        (it.cmd.loc as? TACSymbol.Var)?.meta?.find(TACMeta.DISPLAY_PATHS),
                        (it.cmd.loc as? TACSymbol.Var)?.meta?.find(TACMeta.ACCESS_PATHS)
                    )
                }
                is TACCmd.Simple.AssigningCmd.AssignExpCmd -> {
                    val v = (it.cmd.rhs as TACExpr.Sym.Var).s
                    Triple(
                        v.meta.find(TACMeta.STORAGE_KEY),
                        v.meta.find(TACMeta.DISPLAY_PATHS),
                        v.meta.find(TACMeta.ACCESS_PATHS)
                    )
                }
                else -> `impossible!`
            }
            if(contractInstanceId == null || m.getContainingContract().instanceId != contractInstanceId) {
                return@mapNotNull null
            }
            val id = it.cmd.meta.find(CallGraphBuilder.ContractStorageRead.META_KEY)!!.id
            val fldName = display?.paths?.singleOrNull()?.let {
                it as? DisplayPath.FieldAccess
            }?.field
            val namedAddress = fldName?.let(src.structLinkingInfo::get)
            val rawAddress = path?.paths?.singleOrNull()?.let {
                it as? StorageAnalysis.AnalysisPath.StructAccess
            }?.offset?.takeIf {
                it.bytes == it.words * EVM_WORD_SIZE
            }?.words?.let(src.legacyStructLinking::get)
            if(rawAddress != namedAddress && rawAddress != null && namedAddress != null) {
                logger.warn {
                    "At read $it, disagreement about the link target: $rawAddress ($path) vs $namedAddress ($fldName)"
                }
                return@mapNotNull null
            }
            if(rawAddress != null || namedAddress != null) {
                logger.info {
                    "Resolved read at $it to address ${rawAddress ?: namedAddress}"
                }
            }
            id `to?` (namedAddress ?: rawAddress)
        }.collect(Collectors.groupingBy({ it.first }, Collectors.mapping({ it.second}, Collectors.toSet()))).mapValues {
            it.value.singleOrNull()
        }

        fun CallGraphBuilder.CalledContract.tryResolve(): CallGraphBuilder.CalledContract {
            val storageReadId = (this as? CallGraphBuilder.CalledContract.UnresolvedRead)?.storageReadId ?: return this
            val contractId = resolutions[storageReadId] ?: return this
            return CallGraphBuilder.CalledContract.FullyResolved.StorageLink(contractId, storageReadId)
        }

        val patching = prog.toPatchingProgram()
        prog.parallelLtacStream().filter {
            it.cmd is TACCmd.Simple.ReturnCmd || (it.cmd is TACCmd.Simple.SummaryCmd && it.cmd.summ is CallSummary)
        }.mapNotNull {
            when (it.cmd) {
                is TACCmd.Simple.ReturnCmd -> {
                    val linking = it.cmd.meta.find(TACMeta.RETURN_LINKING) ?: return@mapNotNull null
                    it.ptr to it.cmd.copy(meta = it.cmd.meta + (TACMeta.RETURN_LINKING to linking.copy(
                        byOffset = linking.byOffset.mapValues {
                            it.value.tryResolve()
                        }
                    )))
                }
                is TACCmd.Simple.SummaryCmd -> {
                    check(it.cmd.summ is CallSummary) {
                        "Picked up summary command $it that was *not* a call summary"
                    }
                    it.ptr to it.cmd.copy(
                        summ = it.cmd.summ.copy(
                            callTarget = it.cmd.summ.callTarget.mapToSet { y -> y.tryResolve() },
                            callConvention = it.cmd.summ.callConvention.copy(
                                input = it.cmd.summ.callConvention.input.copy(
                                    rangeToDecomposedArg = it.cmd.summ.callConvention.input.rangeToDecomposedArg.mapValues { (_, arg) ->
                                        arg.withContractReference(
                                            arg.contractReference?.tryResolve()
                                        )
                                    }
                                )
                            )
                        )
                    )
                }
                else -> `impossible!`
            }
        }.sequential().forEach { (where, new) ->
            patching.replaceCommand(where, listOf(new))
        }
        return patching.toCode(prog)
    }

}
