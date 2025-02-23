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

import evm.twoToThe
import java.math.BigInteger

/**
 * The different schemes how we model hash functions.
 */
sealed class HashingScheme : java.io.Serializable {
    companion object {
        private const val defaultLegacyGapSizeExponent = 258

        val defaultLegacyGapSize = twoToThe(defaultLegacyGapSizeExponent)

        /** default hashing scheme when using Int (LIA, NIA,..) logics */
        val DefaultInt = PlainInjectivity

        /** default hashing scheme when using BV logics */
        val DefaultBv = PlainInjectivity
    }

    /** The traditional approach, not obsolete, though; only works with Int logics. */
    data class Legacy(val gapSize: BigInteger = defaultLegacyGapSize) : HashingScheme() {
        companion object {
            const val CONFIG_KEYWORD = "Legacy"
        }
    }

    /** Uses standard injectivity axioms, extended to also cover offset (`hash(x) + o`) expressions.  */
    object PlainInjectivity : HashingScheme() {
        const val CONFIG_KEYWORD = "PlainInjectivity"
        fun readResolve(): Any = PlainInjectivity
    }

    /** Use smtlib theory of datatypes to represent hash-related expressions. */
    object Datatypes : HashingScheme() {
        const val CONFIG_KEYWORD = "Datatypes"
        fun readResolve(): Any = Datatypes
    }

}
