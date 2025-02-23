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

package smt

import datastructures.stdcollections.*
import utils.*
import vc.data.LExpression

sealed class GenerateEnv private constructor() {
    abstract val quantifierScopes: List<LExpression.QuantifiedExpr>

    companion object {
        operator fun invoke(quantifierScopes: List<LExpression.QuantifiedExpr>) =
            if (quantifierScopes.isEmpty()) {
                Empty
            } else {
                NonEmpty(quantifierScopes)
            }

        operator fun invoke() : GenerateEnv = Empty
    }

    private data object Empty : GenerateEnv() {
        override val quantifierScopes: List<LExpression.QuantifiedExpr>
            get() = emptyList()
    }

    private data class NonEmpty(override val quantifierScopes: List<LExpression.QuantifiedExpr>) : GenerateEnv()

    fun pushQuantifier(quantifiedFormula: LExpression.QuantifiedExpr) =
        GenerateEnv(quantifierScopes + quantifiedFormula)

    val quantifiedVariables by lazy {
        quantifierScopes.flatMapToSet { it.quantifiedVar }
    }

    fun merge(other: GenerateEnv) =
        when {
            this == Empty -> other
            other == Empty -> this
            else -> GenerateEnv(this.quantifierScopes + other.quantifierScopes)
        }

    fun isEmpty() = this == Empty
}
