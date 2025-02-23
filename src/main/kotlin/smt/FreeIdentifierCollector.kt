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

import com.certora.collect.*
import datastructures.stdcollections.*
import smt.solverscript.functionsymbols.traverseQuant
import vc.data.LExpression
import java.util.*

/**
 * Collects free identifiers in a given [LExpression].
 * Use via [collect] function.
 * Can optionally cache results (set [withCache] to `true`). The cache is updated for all (non-strict)
 * subexpressions of each [LExpression] that [collect] is called on.
 *
 * A [FreeIdentifierCollector] object can be used multiple times (and must be reused to use the cache).
 */
class FreeIdentifierCollector(withCache: Boolean) {
    private val cache : MutableMap<LExpression, Set<LExpression.Identifier>>? =
        if (withCache) {
            mutableMapOf()
        } else {
            null
        }

    fun collect(exp: LExpression): Set<LExpression.Identifier> {
        // using persistent sets here because the result of a subexpression is part for every super-expression
        // (thus can be shared in memory)
        val result = treapSetBuilderOf<LExpression.Identifier>()
        exp.traverseQuant { e, env ->
            if (e is LExpression.Identifier && e !in env.quantifiedVariables) {
                result.add(e)
            }
            // update the cache for each subexpression that we processed
            cache?.let { map -> map[e] = result.build() }
        }
        return result
    }

}
