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

package smtlibutils.data

import evm.MAX_EVM_INT256
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import smtlibutils.data.Sort.Apply
import smtlibutils.data.SortSymbol.UserDefined
import smtlibutils.statistics.SmtPatterns

internal class UnificationTest {

    @Test
    fun test01() {
        // s = f (x)
        val s = Apply(
            UserDefined(Identifier.Simple("f"), 1),
            listOf(Sort.Param("x"))
        )
        // t = f (_7)
        val t = Apply(
            UserDefined(Identifier.Simple("f"), 1),
            listOf(Sort.Symbol(UserDefined(Identifier.Simple("_7"), 0)))
        )

        val unified = Sort.Unification.unify(s, t)
        assertTrue(unified == t)
    }

    @Test
    fun test02() {
        val x = Sort.Param("x")

        // s = x
        val s = x

        // t = f (x)
        val t = Apply(
            UserDefined(Identifier.Simple("f"), 1),
            listOf(x)
        )


        val unified = Sort.Unification.unify(s, t)
        assertTrue(unified == null)
    }

    @Test
    fun test03() {
        // s = x
        val s = Sort.Param("x")

        // t = y
        val t = Sort.Param("y")

        val unified = Sort.Unification.unify(s, t)
        assertTrue(unified == t || unified == s)
    }

    @Test
    fun test04() {
        val f = UserDefined(Identifier.Simple("f"), 2)
        val g = UserDefined(Identifier.Simple("g"), 1)

        val twelve = Sort.Symbol(UserDefined(Identifier.Simple("_12"), 0))
        val thirteen = Sort.Symbol(UserDefined(Identifier.Simple("_13"), 0))

        // s = f (x, g(12))
        val s = Apply(f, listOf(Sort.Param("x"), Apply(g, listOf(twelve))))

        // t = f ( g(13), g (z))
        val t = Apply(f, listOf(Apply(g, listOf(thirteen)), Apply(g, listOf(Sort.Param("z")))))


        val expected = Apply(f, listOf(Apply(g, listOf(thirteen)), Apply(g, listOf(twelve))))

        val unifier = Sort.Unification.computeUnifier(s, t)
        check(unifier != null)
        val unified = unifier.applyTo(s)

        assertTrue(unifier.applyTo(s) == unifier.applyTo(t))
        assertTrue(unified == expected)
    }

    @Test
    fun test05() {
        val f = UserDefined(Identifier.Simple("f"), 3)
        val x = Sort.Param("x")
        val y = Sort.Param("y")
        val z = Sort.Param("z")

        // s = (f x y z)
        val s = Apply(f, listOf(x, y, z))

        // t = (f z y x)
        val t = Apply(f, listOf(z, y, x))

        val expected1 = Apply(f, listOf(x, y, x))
        val expected2 = Apply(f, listOf(z, y, z))

        val unifier = Sort.Unification.computeUnifier(s, t)
        check(unifier != null)
        val unified = unifier.applyTo(s)

        assertTrue(unifier.applyTo(s) == unifier.applyTo(t))
        assertTrue(unified == expected1 || unified == expected2)
    }

    @Test
    fun test07() {
        val f = UserDefined("f", 2)

        val g = UserDefined("g", 1)

        val x = Sort.Param("x")
        val y = Sort.Param("y")
        val z = Sort.Param("z")

        val twelve = Sort.Symbol.userDefined("_12")
        val thirteen = Sort.Symbol.userDefined("_13")

        // s = (f (g (g 12)) (f y y))
        val s = Apply(f, Apply(g, Apply(g, twelve)), Apply(f, y, y))

        // t = (f x (f (g 13) z))
        val t = Apply(f, x, Apply(f, Apply(g, thirteen), z))
//        val t = Apply(f, x, Apply(f, z, Apply(g, thirteen)))

        // .. f 1 .. { (g (g 12)), x}  => [x -> (g (g 12))]
        // .. f 2 .. f 1 ..  { y, (g 13) } => [y -> (g 13)]
        // .. f 2 .. f 2 .. { y, z } => [y -> z] | [z -> y]


        val expected = Apply(f, Apply(g, Apply(g, twelve)), Apply(f, Apply(g, thirteen), Apply(g, thirteen)))

        val unifier = Sort.Unification.computeUnifier(s, t)
        check(unifier != null)
        assertTrue(unifier.applyTo(s) == unifier.applyTo(t))

        val unified = Sort.Unification.unify(s, t)
        assertTrue(unified == expected)
    }

    @Test
    fun test08() {
        val f = UserDefined("f", 2)

        val g = UserDefined("g", 1)

        val x = Sort.Param("x")
        val y = Sort.Param("y")

        val twelve = Sort.Symbol.userDefined("_12")
        val thirteen = Sort.Symbol.userDefined("_13")

        // s = (f (g (g 12)) (f y y))
        val s = Apply(f, Apply(g, Apply(g, twelve)), Apply(f, y, y))

        // t = (f x (f (g 13) y))
        val t = Apply(f, x, Apply(f, Apply(g, thirteen), y))

        val unifier = Sort.Unification.computeUnifier(s, t)
        check(unifier != null)
        assertTrue(unifier.applyTo(s) == unifier.applyTo(t))

        val expected = Apply(f, Apply(g, Apply(g, twelve)), Apply(f, Apply(g, thirteen), Apply(g, thirteen)))

        val unified = Sort.Unification.unify(s, t)
        assertTrue(unified == expected)
    }

    @Test
    fun test09() {
        val array = UserDefined("array", 2)
        val node = Sort.Symbol.userDefined("node")
        val bool = Sort.Symbol.userDefined("bool")

        val s = Apply(array, node, bool)
        val t = bool
        val unified = Sort.Unification.unify(s, t)
        assertTrue(unified == null)
    }


    // SmtExp-based unification tests


    object SmtExpTestEnv {
        @Suppress("UNUSED_EXPRESSION") // This is strange magic, and Kotlin gets a bit disoriented
        operator fun invoke(make: SmtExpTestEnv.() -> Unit): Unit = make()

        /** Prepares a script with some declared symbols, so those can be used in the tests*/
        private fun prepareScript(): SmtScript {
            val res = SmtScript()
            res.declareConst("x", Sort.IntSort)
            res.declareConst("y", Sort.IntSort)
            res.declareFun("f", listOf(Sort.IntSort), Sort.IntSort)
            res.declareFun("g", listOf(Sort.IntSort, Sort.IntSort), Sort.IntSort)
            return res
        }

        val script = prepareScript()

        fun String.toFs(): SmtFunctionSymbol =
            script.symbolTable.getAllDeclaredFuns().find { it.functionSymbol.name.sym == this }?.functionSymbol
                ?: error("function symbol not declared")

        val f = "f".toFs()
        val g = "g".toFs()
        val x = script.id("x", Sort.IntSort)
        val y = script.id("y", Sort.IntSort)

    }

    @Test
    fun testSmtExp01() {
        SmtExpTestEnv {
            // these two terms unify because they're identical
            val e1 = script { apply(f, x) }
            val e2 = script { apply(f, x) }
            val unifier = SmtExp.Unification(script).computeUnifier(e1, e2)

            assertNotEquals(null, unifier)
        }
    }

    @Test
    fun testSmtExp02() {
        SmtExpTestEnv {
            // these two terms don't unify because they're not identical and there are no placeholder terms (which are
            // the variables to the unification algorithm
            val e1 = script { apply(f, x) }
            val e2 = script { apply(f, y) }
            val unifier = SmtExp.Unification(script).computeUnifier(e1, e2)

            assertEquals(null, unifier)
        }
    }

    @Test
    fun testSmtExp03() {
        SmtExpTestEnv {
            // these two terms don't unify because they're not identical and there are no placeholder terms (which are
            // the variables to the unification algorithm
            val e1 = script { apply(f, x) }
            val e2 = script { apply(f, SmtExp.PlaceHolder("p", Sort.IntSort)) }
            val unifier = SmtExp.Unification(script).computeUnifier(e1, e2)

            assertEquals(e1, unifier?.applyTo(e2))
            assertEquals(1, unifier?.pairs?.size)
        }
    }

    @Test
    fun testSmtExp04() {
        SmtExpTestEnv {
            val e1 = SmtPatterns.isPositiveSignedIntPattern(SmtExp.PlaceHolder("p", Sort.IntSort))
            val e2 = script { apply(f, apply(g, x, y)) le number(MAX_EVM_INT256) }
            val unifier = SmtExp.Unification(script).computeUnifier(e1, e2)

            assertEquals(e2, unifier?.applyTo(e1))
            assertEquals(1, unifier?.pairs?.size)
        }
    }

    @Test
    fun testSmtExp05() {
        SmtExpTestEnv {
            // isPositiveSignedInt(e1) eq isPositiveSignedInt(e2)
            val e1 = SmtPatterns.areOfSameSign(
                SmtExp.PlaceHolder("p", Sort.IntSort),
                SmtExp.PlaceHolder("q", Sort.IntSort)
            )
            val e2 = script {
                (apply(f, apply(g, x, y)) le number(MAX_EVM_INT256)) eq
                        (y le number(MAX_EVM_INT256))
            }
            val unifier = SmtExp.Unification(script).computeUnifier(e1, e2)

            assertEquals(e2, unifier?.applyTo(e1))
            assertEquals(2, unifier?.pairs?.size)
        }
    }

}
