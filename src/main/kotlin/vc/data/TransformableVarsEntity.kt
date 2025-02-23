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

import com.certora.collect.*
import tac.MetaKey
import utils.*
import java.io.Serializable

/*
Question: Let's say I have:

data class Foo(val other: Bar, ...): TransformableSymEntity
data class Bar( ... ): TransformableVarEntity

How do I implement those things? The remapper Foo gets will remap symbols
But the remapper expected by the "other" field will want a var -> var mapper.

Answer: In such a case, Foo should be [TransformableSymAndVarEntity], and with respect to the "other" field, "other"'s symbols
will be mapped using transformVariables:

class Foo(val other: Bar, val a: TACSymbol): TransformableSymAndVarEntity {

    override fun transformVariables(f: (TACSymbol.Var) -> TACSymbol.Var) -> Foo {
        return copy(
            other = this.other.transformSymbols(f)
        )
    }
    override fun transformSymbols(f: (TACSymbol) -> TACSymbol) -> Foo {
        return copy(
            a = f(a)
        )
    }
}

Similar question but with:

data class Foo(val other: Bar, ...): TransformableVarEntity
data class Bar( ... ): TransformableSymEntity

Answer: same, but this time, other will be mapped using transformSymbols:

class Foo(val other: Bar, ...): TransformableSymAndVarEntity {
    override fun transformSymbols(f: (TACSymbol) -> TACSymbol) -> Foo {
        return copy(
            other = this.other.transformSymbols(f)
        )
    }
    override fun transformVariables(f: (TACSymbol.Var) -> TACSymbol.Var) -> Foo {
        return copy(
            a = f(a)
        )
    }
}
 */

/**
 * Entity transformer, which using [transformSymbols] as a mapper
 * over the symbols inside the entity.
 */
@Treapable
interface TransformableEntity<S: TACSymbol, out T: TransformableEntity<S,T>> : Serializable {
    fun transformSymbols(f: (S) -> S): T
}

/**
 * [TransformableEntity] which maps general [TACSymbol]s inside an entity.
 */
interface TransformableSymEntity<out T : TransformableSymEntity<T>> : TransformableEntity<TACSymbol, T>

/**
 * [TransformableEntity] which maps [TACSymbol.Var]s inside an entity.
 * [TransformableVarEntity] and [TransformableSymEntity] are disjoint
 * (cannot be implemented both by the same element).
 */
interface TransformableVarEntity<out T: TransformableVarEntity<T>>: TransformableEntity<TACSymbol.Var, T>

interface WithSupport {
    /**
     * [support] is a set of important [TACSymbol.Var]s we want to keep update during transformations,
     * to have them up-to-date, for example, when calling the DefAnalysis.
     */
    val support: Set<TACSymbol.Var>
}

interface TransformableVarEntityWithSupport<out T : TransformableVarEntityWithSupport<T>> : TransformableVarEntity<T>,
    WithSupport, Serializable

/**
 * [TransformableSymEntity] with a support, which get updated dynamically when being accessed.
 */
interface TransformableSymEntityWithRlxSupport<out T : TransformableSymEntityWithRlxSupport<T>> :
    TransformableSymEntity<T>, Serializable, WithSupport {

    val relaxedSupport: Set<TACSymbol.Var>
        get() {
            val ret = mutableSetOf<TACSymbol.Var>()
            transformSymbols { s ->
                if (s is TACSymbol.Var) {
                    ret.add(s)
                }
                s
            }
            return ret
        }

    override val support: Set<TACSymbol.Var>
        get() = relaxedSupport
}

/**
 * [TransformableSymEntity] which is able to map both [TACSymbol] to [TACSymbol] and
 * [TACSymbol.Var] to [TACSymbol.Var].
 */
interface TransformableSymAndVarEntity<out T : TransformableSymAndVarEntity<T>> : TransformableSymEntity<T> {
    fun transformVariables(f: (TACSymbol.Var) -> TACSymbol.Var): T
}

/**
 * [TransformableSymAndVarEntity] with a support, where the support consist of a strict/constant part
 * [strictSupport] and dynamically part [relaxedSupport].
 */
interface TransformableSymAndVarEntityWithSupport<out T : TransformableSymAndVarEntityWithSupport<T>> :
    TransformableSymAndVarEntity<T>, TransformableSymEntityWithRlxSupport<T> {

    val strictSupport: Set<TACSymbol.Var>

    override val support: Set<TACSymbol.Var>
        get() = strictSupport + relaxedSupport
}

/**
 * Applies the entity-transformers [mapSymbol], [mapVar] on [v] based on its type.
 * The result of the applications is expected to be the same class as the class of [k].
 * Otherwise, RuntimeException is thrown.
 */
fun applyTransEntityMappers(
    v: Serializable,
    k: MetaKey<*>,
    mapSymbol: (TACSymbol) -> TACSymbol,
    mapVar: (TACSymbol.Var) -> TACSymbol.Var
): Serializable {
    val ret = if (v is TransformableVarEntity<*>) {
        v.transformSymbols(mapVar)
    } else if (v is TransformableSymEntity<*>) {
        v.transformSymbols(mapSymbol).let {
            if (it is TransformableSymAndVarEntity<*>) {
                it.transformVariables(mapVar)
            } else {
                it
            }
        }
    } else {
        v
    }
    if (!(k.typ.isInstance(ret))) {
        throw RuntimeException(
            "the transformable entity ($v) failed to return the right type when applying a " +
                    "TransformableEntity transformation: should have that $k ${k.typ} is an instance of $ret (${ret.javaClass.name})"
        )
    } else {
        return ret
    }
}
