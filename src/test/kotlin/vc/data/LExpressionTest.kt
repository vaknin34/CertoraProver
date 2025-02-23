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

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import smt.FreeIdentifierCollector
import smt.solverscript.functionsymbols.TheoryFunctionSymbol
import smt.solverscript.functionsymbols.contains
import smt.solverscript.functionsymbols.getFreeIdentifiers
import tac.Tag

internal class LExpressionTest {

    private fun id(s: String, t: Tag) = LExpression.Identifier(s, t)

    private fun quant(q: Quantifier, i: LExpression.Identifier, b: LExpression) =
        LExpression.QuantifiedExpr(q, listOf(i), b)

    private fun exists(i: LExpression.Identifier, b: () -> LExpression) = quant(Quantifier.EXISTS, i, b())

    private infix fun LExpression.lt(r: LExpression) =
        LExpression.ApplyExpr(TheoryFunctionSymbol.Binary.IntLt, this, r)

    private infix fun LExpression.and(r: LExpression) =
        LExpression.ApplyExpr(TheoryFunctionSymbol.Vec.LAnd, this, r)

    val x = id("x", Tag.Bit256)
    val y = id("y", Tag.Bit256)

    val cachedFreeIdCollector = FreeIdentifierCollector(withCache = true)

    @Test
    fun getFreeVars01() {
        val formula = exists(x) { x lt y }
        assertEquals(setOf(y), formula.getFreeIdentifiers())
        assertEquals(setOf(y), cachedFreeIdCollector.collect(formula))
    }

    @Test
    fun getFreeVars02() {
        val formula = (x lt y) and exists(x) { x lt y }
        assertEquals(setOf(x, y), formula.getFreeIdentifiers())
        assertEquals(setOf(x, y), cachedFreeIdCollector.collect(formula))
    }

    @Test
    fun getFreeVars03() {
        val z = id("z", Tag.Bit256)
        val formula = exists(x) { exists(x) { x lt y } and (x lt z) }
        assertEquals(setOf(y, z), formula.getFreeIdentifiers())
        assertEquals(setOf(y, z), cachedFreeIdCollector.collect(formula))
    }

    @Test
    fun contains1() {
        val formula = (x lt y) and exists(x) { x lt y }
        assert(formula.contains { it is LExpression.QuantifiedExpr })
    }

    @Test
    fun contains2() {
        val formula = (x lt y) and exists(x) { x lt y }
        assert(!formula.contains { it is LExpression.Literal && it.tag is Tag.Bool })
    }

}
