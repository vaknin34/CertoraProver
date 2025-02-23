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

package vc.data

import allocator.Allocator
import allocator.GenerateRemapper
import allocator.GeneratedBy
import analysis.ip.InternalFuncArg
import analysis.ip.InternalFuncRet
import analysis.ip.InternalFunctionStartInfo
import spec.cvlast.QualifiedMethodSignature
import datastructures.stdcollections.*
import utils.*

@KSerializable
@GenerateRemapper
data class InternalCallSummary(
    @GeneratedBy(Allocator.Id.INTERNAL_CALL_SUMMARY, source = true)
    val id: Int,
    val signature: QualifiedMethodSignature,
    val internalArgs: List<InternalFuncArg>,
    val internalExits: List<InternalFuncRet>,
    val callSrc: TACMetaInfo?
) : TACSummary, InternalFunctionStartInfo, AssigningSummary, RemapperEntity<InternalCallSummary> {
    override val variables: Set<TACSymbol.Var>
        get() = support
    override val annotationDesc: String
        get() = "Internal function call to $signature to be summarized later"

    override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): InternalCallSummary {
        return InternalCallSummary(
            signature = signature,
            internalArgs = internalArgs.map {
                it.transformSymbols(f)
            },
            internalExits = internalExits.map {
                it.transformSymbols(f)
            },
            callSrc = callSrc,
            id = id
        )
    }

    private val support: Set<TACSymbol.Var>
        get() = internalArgs.flatMapToSet {
            it.support
        } + internalExits.flatMapToSet {
            it.support
        }
    override val methodSignature: QualifiedMethodSignature
        get() = signature
    override val callSiteSrc: TACMetaInfo?
        get() = callSrc
    override val args: List<InternalFuncArg>
        get() = internalArgs
    override val mayWriteVars: Collection<TACSymbol.Var>
        get() = listOf()
    override val mustWriteVars: Collection<TACSymbol.Var>
        get() = internalExits.mapToSet { it.s }
}
