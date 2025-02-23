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

@file:kotlinx.serialization.UseSerializers(utils.BigIntegerSerializer::class)
package sbf.tac

import sbf.cfg.SbfType
import tac.MetaKey
import com.certora.collect.*
import datastructures.stdcollections.*
import utils.AmbiSerializable
import utils.HasKSerializable
import vc.data.TACSymbol
import utils.KSerializable
import vc.data.TransformableVarEntityWithSupport

val SBF_INLINED_FUNCTION_START = MetaKey<SbfInlinedFuncStartAnnotation>("sbf.inline.start")
val SBF_INLINED_FUNCTION_END = MetaKey<SbfInlinedFuncEndAnnotation>("sbf.inline.end")

// This should be an enum, but enums do not have stable hash codes.
@KSerializable
@Treapable
sealed class SbfArgSort: HasKSerializable, AmbiSerializable {
    /** Scalars that are definitely not pointers **/
    @KSerializable
    object SCALAR: SbfArgSort() {
        override fun hashCode(): Int = utils.hashObject(this)
        private fun readResolve(): Any = SCALAR
        override fun toString(): String = "SCALAR"
    }

    /** Pointers can be any of heap/global (we scalaraize the stack) **/
    @KSerializable
    object POINTER: SbfArgSort() {
        override fun hashCode(): Int = utils.hashObject(this)
        private fun readResolve(): Any = POINTER
        override fun toString(): String = "POINTER"
    }

    /**
     * The inferred type is not precise enough to conclude the value
     * is definitely a scalar or a pointer
     */
    @KSerializable
    object UNKNOWN: SbfArgSort() {
        override fun hashCode(): Int = utils.hashObject(this)
        private fun readResolve(): Any = UNKNOWN
        override fun toString(): String = "UNKNOWN"
    }

    companion object {
        fun fromSbfType(t: SbfType): SbfArgSort {
            return when (t) {
                is SbfType.NumType -> SCALAR
                is SbfType.PointerType -> POINTER
                else -> UNKNOWN
            }
        }
    }
}

/**
 * @property sort: based on observed uses, a guess as to the sort of the argument
 * @property observedUse: whether this value appears to be used at a particular inlined call
 */
@KSerializable
@Treapable
data class SbfFuncArgInfo(
    val sort: SbfArgSort,
    val observedUse: Boolean,
): HasKSerializable, AmbiSerializable

/**
 * @property name the  name of the inlined function
 * @property id identifies this inlining instance (to match with the corresponding End annotation
 * @property args a guess as to the variables used as arguments.
 */
@KSerializable
@Treapable
data class SbfInlinedFuncStartAnnotation(
    val name: String,
    val id: Int,
    val args: List<Pair<TACSymbol.Var, SbfFuncArgInfo>>,
): HasKSerializable, AmbiSerializable,
   TransformableVarEntityWithSupport<SbfInlinedFuncStartAnnotation> {
    override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): SbfInlinedFuncStartAnnotation {
        return this.copy(args = args.map {
            it.copy(first = f(it.first))
        })
    }

    override val support: Set<TACSymbol.Var>
        get() = args.unzip().first.toSet()
}

/**
 * @property name the  name of the inlined function
 * @property id identifies this inlining instance
 * @property retVal the variable to which the return value is assigned
 */
@KSerializable
@Treapable
data class SbfInlinedFuncEndAnnotation(
    val name: String,
    val id: Int,
    val retVal: TACSymbol.Var,
): HasKSerializable, AmbiSerializable
