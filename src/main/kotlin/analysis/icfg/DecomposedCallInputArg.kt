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

package analysis.icfg

import analysis.LTACSymbol
import com.certora.collect.*
import tac.DecomposedInputScalarSort
import tac.TACBasicMeta
import tac.Tag
import utils.*
import vc.data.TACSymbol
import vc.data.UniqueIdEntity
import java.io.Serializable
import java.math.BigInteger

/**
 *
 * An input argument that has been successfully decomposed from the scratch memory by the [CallGraphBuilder].
 * We still have to make sure that the writes to this variable are patched up to include the assignment to [v],
 * which is going to be passed as an argument to the callee.
 */
@Treapable
data class DecomposedArgVariableWithSourceWrites(

    /**
     * The set of TACSymbols written to scratch memory, each of which
     * is an input argument (before being decomposed)
     * before the external call. Note: there could be more than one symbol due to joins
     * (as a result, e.g., branching in the program).
     */
    val scratchWriteSymbols: Set<LTACSymbol>,

    /**
     * The "fun input" symbol
     */
    val v: TACSymbol.Var
) : Serializable {

    companion object {
        fun decompVarName(t: Tag, byteOffset: BigInteger, summaryId: Int): TACSymbol.Var {
            check(t.isPrimitive()) { "Currently, decomposed inputs can only have primitive types; got $t" }
            return TACSymbol.Var(
                "funCallInput!$summaryId!${byteOffset}",
                t
            ).withMeta(
                TACBasicMeta.DECOMP_INPUTSCALAR_SORT,
                DecomposedInputScalarSort.Simple(byteOffset)
            )
        }

    }
}

/**
 * Represents a decomposed argument including information about:
 * - The original range in the memory scratch buffer to which it was written
 * - (optionally) if it holds the value of a contract reference
 * - the [TACSymbol.Var] object that is going to be passed to the callee's calldata as part of inlining
 */
@KSerializable
@Treapable
sealed class DecomposedCallInputArg : AmbiSerializable, UniqueIdEntity<DecomposedCallInputArg> {
    /**
     * The original range of scratch memory bytes where this input argument was stored
     */
    abstract val scratchRange: ScratchByteRange

    abstract val contractReference: CallGraphBuilder.CalledContract?

    override fun mapId(f: (Any, Int, () -> Int) -> Int): DecomposedCallInputArg {
        return contractReference?.mapId(f)?.let(this::withContractReference) ?: this
    }

    /**
     * Scalarized input arguments, available to the callee in
     * the form of a variable symbol ([Variable.v]).
     */
    @KSerializable
    data class Variable(
        override val scratchRange: ScratchByteRange,
        override val contractReference: CallGraphBuilder.CalledContract?,
        val v: TACSymbol.Var
    ) : DecomposedCallInputArg() {

        override fun withContractReference(contractReference: CallGraphBuilder.CalledContract?): DecomposedCallInputArg {
            return this.copy(contractReference = contractReference)
        }

       fun copyWithVarMapper(
            varMapper: (TACSymbol.Var) -> TACSymbol.Var
        ) = copy(
            v = varMapper(v)
        )
    }

    /**
     * Scalaraized input arguments, available to the callee in the form of a literal ([Constant.c]).
     */
    @KSerializable
    data class Constant(
        override val scratchRange: ScratchByteRange,
        override val contractReference: CallGraphBuilder.CalledContract?,
        val c: TACSymbol.Const
    ) : DecomposedCallInputArg() {
        override fun withContractReference(contractReference: CallGraphBuilder.CalledContract?): DecomposedCallInputArg {
            return this.copy(contractReference = contractReference)
        }

    }

    abstract fun withContractReference(contractReference: CallGraphBuilder.CalledContract?) : DecomposedCallInputArg

    fun getSymbol() =
        when (this) {
            is Constant -> this.c
            is Variable -> this.v
        }

    //TODO: Add mapping type arguments
}
