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
package analysis.pta.abi

import analysis.ptaInvariant
import com.certora.collect.*
import utils.*
import vc.data.TACSymbol
import java.io.Serializable
import java.math.BigInteger

@Treapable
sealed class ObjectPathGen<@Treapable T : Serializable> : Serializable {
    data class Root<@Treapable T : Serializable>(val oRoot: T) : ObjectPathGen<T>() {
        override val root: T
            get() = oRoot
    }

    data class Field<@Treapable T : Serializable>(override val parent: ObjectPathGen<T>, val offset: BigInteger) : ObjectPathGen<T>(),
        WithParentPath<T> {
        lateinit var parentCache: T
        override val root: T
            get() {
                if(!this::parentCache.isInitialized) {
                    parentCache = this.parent.root
                }
                return parentCache
            }

        override fun mapParent(newParent: ObjectPathGen<T>): ObjectPathGen<T> {
            return copy(parent = newParent)
        }
    }

    data class StaticArrayField<@Treapable T : Serializable>(override val parent: ObjectPathGen<T>) : ObjectPathGen<T>(), WithParentPath<T> {
        lateinit var parentCache: T
        override val root: T
            get() {
                if(!this::parentCache.isInitialized) {
                    parentCache = this.parent.root
                }
                return parentCache
            }

        override fun mapParent(newParent: ObjectPathGen<T>): ObjectPathGen<T> {
            return this.copy(parent = newParent)
        }
    }

    data class ArrayElem<@Treapable T : Serializable>(override val parent: ObjectPathGen<T>) : ObjectPathGen<T>(), WithParentPath<T> {
        override fun mapParent(newParent: ObjectPathGen<T>): ObjectPathGen<T> {
            return this.copy(
                    parent = newParent
            )
        }

        lateinit var parentCache: T
        override val root: T
            get() {
                if(!this::parentCache.isInitialized) {
                    parentCache = this.parent.root
                }
                return parentCache
            }
    }

    data class ArrayLength<@Treapable T : Serializable>(override val parent: ObjectPathGen<T>) : ObjectPathGen<T>(), WithParentPath<T> {
        override fun mapParent(newParent: ObjectPathGen<T>): ObjectPathGen<T> {
            return this.copy(
                    parent = newParent
            )
        }

        lateinit var parentCache: T
        override val root: T
            get() {
                if(!this::parentCache.isInitialized) {
                    parentCache = this.parent.root
                }
                return parentCache
            }
    }

    abstract val root: T

    fun joinOrNull(other: ObjectPathGen<T>) : ObjectPathGen<T>? {
        if(this.root != other.root) {
            return null
        }
        if(this === other) {
            return this
        }
        if(this is Field && other is StaticArrayField) {
            return other.joinOrNull(this)
        }
        if(this is StaticArrayField && other is Field) {
            val p = this.parent.joinOrNull(other.parent) ?: return null
            return StaticArrayField(p)
        }
        if(this.javaClass != other.javaClass) {
            return null
        }
        return when(this) {
            is ArrayElem -> {
                check(other is ArrayElem)
                this.parent.joinOrNull(other.parent)?.let(::ArrayElem)
            }
            is Field -> {
                check(other is Field)
                this.parent.joinOrNull(other.parent)?.let { p ->
                    if(other.offset != this.offset) {
                        StaticArrayField(p)
                    } else {
                        Field(offset = this.offset, parent = p)
                    }
                }
            }
            is StaticArrayField -> {
                check(other is StaticArrayField)
                this.parent.joinOrNull(other.parent)?.let(::StaticArrayField)
            }
            is Root -> {
                ptaInvariant(this == other) {
                    "Our variables should have matched and Roots have no other state"
                }
                this
            }
            is ArrayLength -> {
                check(other is ArrayLength)
                this.parent.joinOrNull(other.parent)?.let(::ArrayLength)
            }
        }
    }

    fun transformVariables(f: (TACSymbol.Var) -> TACSymbol.Var, rootMap: (T, (TACSymbol.Var) -> TACSymbol.Var) -> T) : ObjectPathGen<T> {
        return if(this is WithParentPath<*>) {
            this.uncheckedAs<WithParentPath<T>>().let { it.mapParent(it.parent.transformVariables(f, rootMap)) }
        } else {
            check(this is Root) {
                "Expected path $this without parent to be ObjectPath.Root"
            }
            Root(rootMap(this.oRoot, f))
        }
    }
}

fun ObjectPathGen<ObjectPathAnalysis.ObjectRoot>.transformVariables(f: (TACSymbol.Var) -> TACSymbol.Var) = this.transformVariables(f) { oRoot, tF ->
    when(oRoot) {
        is ObjectPathAnalysis.ObjectRoot.CalldataRoot ->
            ObjectPathAnalysis.ObjectRoot.CalldataRoot(
                oRoot.bp.transformVariables(
                    tF
                ), fieldDepth = oRoot.fieldDepth
            )
        is ObjectPathAnalysis.ObjectRoot.V -> ObjectPathAnalysis.ObjectRoot.V(tF(oRoot.v))
    }
}
val ObjectPathGen<ObjectPathAnalysis.ObjectRoot>.rootVar: TACSymbol.Var? get() = (root as? ObjectPathAnalysis.ObjectRoot.V)?.v

@Treapable
object UnitPath : Serializable {
    override fun hashCode() = hashObject(this)
    fun readResolve(): Any = UnitPath
}
