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

package analysis.pta


interface Semantics<in R, out U> {
    operator fun invoke(vararg args: R) : U
}

interface ProviderSemantics<R, U> {
    operator fun invoke(binSemantics: (R, R) -> U, vararg  args: R) : U
}

@Suppress("FunctionName")
fun <R, U> ArithmeticSemantics(lazyHandler: (R) -> Unit, isPointerP: (R) -> Boolean, pointerArithResult: U, vecSemantics: U) : ProviderSemantics<R, U> =
        object : ProviderSemantics<R, U> {
            override fun invoke(binSemantics: (R, R) -> U, vararg args: R): U {
                args.forEach(lazyHandler)
                for (it in args) {
                    if(isPointerP(it)) {
                        return pointerArithResult
                    }
                }

                return if(args.size == 2) {
                    // expected to coerce to ints if they are lazy
                    binSemantics(args[0], args[1])
                } else {
                    vecSemantics
                }
            }
        }

@Suppress("FunctionName")
fun <R, U> ArithmeticSemantics(lazyHandler: (R) -> Unit, isPointerP: (R) -> Boolean, pointerArithResult: U, vecSemantics: U, binSemantics: (R, R) -> U) : Semantics<R, U> =
        ArithmeticSemantics(lazyHandler, isPointerP, pointerArithResult, vecSemantics).let { wrapped ->
            object : Semantics<R, U> {
                override fun invoke(vararg args: R): U = wrapped.invoke(binSemantics, *args)
            }
        }
