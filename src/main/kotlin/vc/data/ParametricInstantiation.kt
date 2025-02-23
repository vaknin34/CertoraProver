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

import bridge.EVMExternalMethodInfo
import utils.CollectingResult
import utils.CollectingResult.Companion.bind
import utils.CollectingResult.Companion.flatten
import utils.CollectingResult.Companion.lift
import utils.CollectingResult.Companion.map
import vc.data.ParametricInstantiation.DataWithMethodParameterInstantiation

/**
 * A [ParametricMethodInstantiatedCode] represents the rules generated over the cross product of all parametric methods.
 *
 * @implementation Each member of [withMethodParamInsts] represents an equivalent rule, except for which
 * method was inserted for calls to each parametric method.
 *
 * @see [DataWithMethodParameterInstantiation]
 */
data class ParametricInstantiation<out T>(val withMethodParamInsts: List<DataWithMethodParameterInstantiation<T>>) {
    data class DataWithMethodParameterInstantiation<out T>(
        val tacCode: T,
        val instantiation: MethodParameterInstantiation
    )

    companion object {
        infix fun ParametricInstantiation<CVLTACProgram>.andThen(other: CVLTACProgram) = this.transformCode {
            mergeCodes(it, other)
        }

        fun <T, U> ParametricInstantiation<T>.bind(f: (x: T) -> ParametricInstantiation<U>) : ParametricInstantiation<U> {
            val toReturn = mutableListOf<DataWithMethodParameterInstantiation<U>>()
            for(d in withMethodParamInsts) {
                for(gen in f(d.tacCode).withMethodParamInsts) {
                    if (gen.instantiation conflictsWith d.instantiation) {
                        continue
                    }
                    toReturn.add(DataWithMethodParameterInstantiation(
                        tacCode = gen.tacCode,
                        instantiation = gen.instantiation + d.instantiation
                    ))
                }
            }
            return ParametricInstantiation(toReturn)
        }

        fun <T, E> ParametricInstantiation<CollectingResult<T, E>>.flatten() = this.withMethodParamInsts.map { instantiation ->
            instantiation.tacCode.bind { tacCode ->
                DataWithMethodParameterInstantiation(tacCode, instantiation.instantiation).lift()
            }
        }.flatten().map {
            ParametricInstantiation(it)
        }

        fun <T> getSimple(c: T) = ParametricInstantiation(listOf(DataWithMethodParameterInstantiation(c, MethodParameterInstantiation.Empty)))

        fun <T> T.toSimple() = getSimple(this)

        fun <T, U, Z> ParametricInstantiation<U>.merge(other: ParametricInstantiation<T>, combiner: (Z, Z) -> Z) : ParametricInstantiation<Z> where U : Z, T : Z {
            val toRet = mutableListOf<DataWithMethodParameterInstantiation<Z>>()
            for(a in this.withMethodParamInsts) {
                for(b in other.withMethodParamInsts) {
                    if(a.instantiation conflictsWith b.instantiation) {
                        continue
                    } else {
                        toRet.add(DataWithMethodParameterInstantiation(combiner(a.tacCode, b.tacCode), a.instantiation + b.instantiation))
                    }
                }
            }
            return ParametricInstantiation(toRet)
        }

        /*
          not the most efficient way to implement this, to be sure...
         */
        fun <T> List<ParametricInstantiation<T>>.flatten() : ParametricInstantiation<List<T>> {
            return this.map {
                it.transformCode {i ->
                    listOf(i)
                }
            }.let {
                mergeMany(it, listOf()) { a, b -> a + b }
            }
        }

        fun <T> List<ParametricInstantiation<T>>.commute() : ParametricInstantiation<T> {
            return ParametricInstantiation(this.flatMap {
                it.withMethodParamInsts
            })
        }

        fun <T, U, Z, X> ParametricInstantiation<U>.merge(second: ParametricInstantiation<T>, third: ParametricInstantiation<Z>, combiner: (X, X, X) -> X) : ParametricInstantiation<X> where T : X, U : X, Z : X {
            return this.withMethodParamInsts.flatMap { instantiation1 ->
                second.withMethodParamInsts.flatMap { instantiation2 ->
                    third.withMethodParamInsts.mapNotNull { instantiation3 ->
                        if (instantiation1.instantiation conflictsWith instantiation2.instantiation ||
                            instantiation1.instantiation conflictsWith instantiation3.instantiation ||
                            instantiation2.instantiation conflictsWith instantiation3.instantiation) {
                            null
                        } else {
                            DataWithMethodParameterInstantiation(
                                combiner(instantiation1.tacCode, instantiation2.tacCode, instantiation3.tacCode),
                                instantiation1.instantiation + instantiation2.instantiation + instantiation3.instantiation
                            )
                        }
                    }
                }
            }.let(::ParametricInstantiation)
        }

        fun <U> mergeMany(codes: List<ParametricInstantiation<U>>, id: U, combiner: (U, U) -> U) : ParametricInstantiation<U> {
            if(codes.isEmpty()) {
                return ParametricInstantiation(listOf(DataWithMethodParameterInstantiation(id, MethodParameterInstantiation.Empty)))
            }
            if(codes.size == 1) {
                return codes.first().let {
                    ParametricInstantiation(it.withMethodParamInsts)
                }
            }
            var init : ParametricInstantiation<U> = codes[0].merge(codes[1], combiner)
            for(i in 2..codes.lastIndex) {
                init = init.merge(codes[i], combiner)
            }
            return init
        }

        fun <T> T.toInstantiation(k: TACSymbol.Var, m: EVMExternalMethodInfo) = ParametricInstantiation(listOf(
            DataWithMethodParameterInstantiation(
                instantiation = MethodParameterInstantiation(mapOf(k to m)),
                tacCode = this
            )
        ))
    }

    fun getAsSimple(): T {
        if (withMethodParamInsts.size == 1) {
            return withMethodParamInsts.first().tacCode
        }

        throw Exception("Can't get as simple $this with size ${withMethodParamInsts.size}")
    }

    fun <U> transform(transform: (DataWithMethodParameterInstantiation<T>) -> DataWithMethodParameterInstantiation<U>): ParametricInstantiation<U> =
        ParametricInstantiation(withMethodParamInsts.map { instantiatedProgram ->
            transform(instantiatedProgram)
        })

    fun <U> transformCode(transform: (T) -> U): ParametricInstantiation<U> =
        transform { instantiatedProgram ->
            DataWithMethodParameterInstantiation(tacCode = transform(instantiatedProgram.tacCode), instantiation = instantiatedProgram.instantiation)
        }

    fun nonEmpty(): ParametricInstantiation<T>? = this.takeIf {
        it.withMethodParamInsts.isNotEmpty()
    }

    fun <U> mapNotNull(transform: (T) -> U?) : ParametricInstantiation<U> =
        this.withMethodParamInsts.mapNotNull innerMap@{
            DataWithMethodParameterInstantiation(
                tacCode = transform(it.tacCode) ?: return@innerMap null,
                instantiation = it.instantiation
            )
        }.let(::ParametricInstantiation)
}
