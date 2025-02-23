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

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import smt.solverscript.LExpressionFactory
import tac.Tag
import vc.data.LExpression

class QuantifierSimplifierTest {
    val lxf = LExpressionFactory()
    val x = LExpression.Identifier("x", Tag.Bit256)
    val y = LExpression.Identifier("y", Tag.Bit256)
    val z = LExpression.Identifier("z", Tag.Bit256)
    val c = lxf.const("c", Tag.Bit256)
    val d = lxf.const("d", Tag.Bit256)
    val e = lxf.const("e", Tag.Bit256)
    val simplifier = QuantifierSimplifier(lxf)

    @Test
    fun testSimplifyExists() {
        val f = lxf {
            exists(x) { eq(x, litInt(13)) and (x lt c) }
        }
        Assertions.assertEquals(lxf { litInt(13) lt c }, simplifier.simplify(f))
    }

    @Test
    fun testSimplifyForallImplies() {
        val f = lxf {
            forall(x) { eq(x, litInt(13)) implies  (x lt c) }
        }
        Assertions.assertEquals(lxf { litInt(13) lt c }, simplifier.simplify(f))
    }

    @Test
    fun testSimplifyForallBinaryDisjunction() {
        val f = lxf {
            forall(x) { not(eq(x, litInt(13))) or  (x lt c) }
        }
        Assertions.assertEquals(lxf { litInt(13) lt c }, simplifier.simplify(f))
    }

    @Test
    fun testSimplifyForallNaryDisjunction01() {
        val f = lxf {
            forall(x) { or(
                not(eq(x, litInt(13))),
                (x lt c),
                (d ge x),
                (d lt e),
            ) }
        }
        Assertions.assertEquals(
            lxf {
                or(
                    litInt(13) lt c,
                    d ge litInt(13),
                    d lt e,
                )
            },
            simplifier.simplify(f)
        )
    }

    @Test
    fun testSimplifyForallNaryDisjunction02() {
        val f = lxf {
            forall(x) { or(
                (x lt c),
                (d ge x),
                not(eq(x, litInt(13))),
                (d lt e),
            ) }
        }
        Assertions.assertEquals(
            lxf {
                or(
                    litInt(13) lt c,
                    d ge litInt(13),
                    d lt e,
                )
            },
            simplifier.simplify(f)
        )
    }


    @Test
    fun testSimplifyExistsUnused() {
        val f = lxf {
            forall(x, y, z) { eq(x, litInt(13)) implies  (x lt c) }
        }
        Assertions.assertEquals(lxf { litInt(13) lt c }, simplifier.simplify(f))
    }

    @Test
    fun testSimplifyForallUnused() {
        val f = lxf {
            forall(x, y, z) { eq(y, litInt(13)) implies  (y lt c) }
        }
        Assertions.assertEquals(lxf { litInt(13) lt c }, simplifier.simplify(f))
    }



    @Test
    fun testDontSimplifyForallWrongPolarity() {
        val f = lxf {
            forall(x) { eq(x, litInt(13)) or  (x lt c) } // equation has the wrong polarity
        }
        Assertions.assertEquals(f, simplifier.simplify(f))
    }

    @Test
    fun testDontSimplifyExistsWrongPolarity() {
        val f = lxf {
            exists(x) { not(eq(x, litInt(13))) and (y lt c) } // equation has the wrong polarity
        }
        Assertions.assertEquals(f, simplifier.simplify(f))
    }

    @Test
    fun testDontSimplifyForallWrongJunctor() {
        val f = lxf {
            forall(x) { not(eq(x, litInt(13))) and (x lt c) } // body has wrong junctor
        }
        Assertions.assertEquals(f, simplifier.simplify(f))
    }

    @Test
    fun testDontSimplifyExistsWrongJunctor01() {
        val f = lxf {
            exists(x) { eq(x, litInt(13)) implies (x lt c) } // body has wrong junctor
        }
        Assertions.assertEquals(f, simplifier.simplify(f))
    }

    @Test
    fun testDontSimplifyExistsWrongJunctor02() {
        val f = lxf {
            exists(x) { eq(x, litInt(13)) or (x lt c) } // body has wrong junctor
        }
        Assertions.assertEquals(f, simplifier.simplify(f))
    }

    @Test
    fun testDontSimplifySingleEquality() {
        lxf {
            listOf(
                exists(x) { eq(x, litInt(13)) }, // not a conjunction
                forall(x) { not(eq(x, litInt(13))) }, // not a conjunction
            ).forEach { f ->
                Assertions.assertEquals(f, simplifier.simplify(f))
            }
        }

        val f1 = lxf { exists(x) { and(eq(x, litInt(13))) } } // not a proper conjunction (conjunction itself will be simplified though)
        Assertions.assertEquals(lxf { exists(x) { eq(x, litInt(13)) } }, simplifier.simplify(f1))

        val f2 = lxf { forall(x) { or(not(eq(x, litInt(13)))) } } // not a proper disjunction (disjunction itself will be simplified though)
        Assertions.assertEquals(lxf { forall(x) { not(eq(x, litInt(13))) } }, simplifier.simplify(f2))
    }

    @Test
    fun testDontSimplifyQVarNotIsolated() {
        val lit13 = lxf.lit256(13)
        val f1 = lxf {
            exists(x) { eq(x, (x add lit13)) and (x lt c) }  // qVar appears on both sides
        }
        Assertions.assertEquals(f1, simplifier.simplify(f1))
        val f2 = lxf {
            forall(x) { not(eq(x, (x add lit13))) or  (x lt c) } // qVar appears on both sides
        }
        Assertions.assertEquals(f2, simplifier.simplify(f2))

        // mixed cases -- these should simplify as there is a usable equality next to the unusable one
        val f3 = lxf {
            exists(x) { and(
                eq(x, lit13),
                eq(x, (x add lit13)),
                (x lt c))
            }
        }
        Assertions.assertEquals(
            lxf { eq(lit13, (lit13 add lit13)) and (lit13 lt c) },
            simplifier.simplify(f3)
        )

        val f4 = lxf {
            forall(x) { or(
                eq(x, (x add lit13)),
                not(eq(x, lit13)),
                x lt c
            ) }
        }
        Assertions.assertEquals(
            lxf {
                or(
                    eq(
                        lit13,
                        (lit13 add lit13)
                    ),
                    lit13 lt c
                )
            },
            simplifier.simplify(f4)
        )
    }

    @Test
    fun testMultipleDerApplications() {
        // .. next to each other
        val f1 = lxf {
            exists(x) { eq(x, litInt(13)) and (x lt c) }  and
                forall(x) { not(eq(x, litInt(14))) or  (x gt c) }
        }
        Assertions.assertEquals(lxf { (litInt(13) lt c) and (litInt(14) gt c)  }, simplifier.simplify(f1))
        // .. nested  (with shadowing)
        val f2 = lxf {
            exists(x) {
                and(
                    eq(x, litInt(13)),
                    (x lt c),
                    forall(x) { not(eq(x, litInt(14))) or (x gt c) }
                )
            }
        }
        Assertions.assertEquals(lxf { (litInt(13) lt c) and (litInt(14) gt c)  }, simplifier.simplify(f2))
        // .. nested  (without shadowing)
        val f3 = lxf {
            exists(x) {
                and(
                    eq(x, litInt(13)),
                    (x lt c),
                    forall(y) { not(eq(y, litInt(14))) or (y gt c) }
                )
            }
        }
        Assertions.assertEquals(lxf { (litInt(13) lt c) and (litInt(14) gt c)  }, simplifier.simplify(f3))
        // .. nested, with shadowing, the inner one can't be eliminated
        val f4 = lxf {
            exists(x) {
                and(
                    eq(x, litInt(13)),
                    (x lt c),
                    forall(x) { not(x lt litInt(14)) or (x gt c) }
                )
            }
        }
        Assertions.assertEquals(lxf { (litInt(13) lt c) and forall(x) { not(x lt litInt(14)) or (x gt c) }  }, simplifier.simplify(f4))
    }


    // for motivation of these tests see https://certora.atlassian.net/browse/CERT-2953
    //  -- we want to be robust to when Identifier.Constant and ~.Variable are mixed up

    @Test
    fun testSimplifyExistsVarVsConst01() {
        val f = lxf {
            exists(x) { eq(x, litInt(13)) and (lxf.const("x", Tag.Bit256) lt c) }
        }
        Assertions.assertEquals(lxf { litInt(13) lt c }, simplifier.simplify(f))
    }

    @Test
    fun testSimplifyExistsVarVsConst02() {
        val f = lxf {
            exists(x) { eq(lxf.const("x", Tag.Bit256), litInt(13)) and (x lt c) }
        }
        Assertions.assertEquals(lxf { litInt(13) lt c }, simplifier.simplify(f))
    }

    @Test
    fun testMultipleDefs01() {
        val f1 = lxf {
            exists(x) { and(eq(x, litInt(13)), eq(x, litInt(14)), (x lt c)) }
        }
        Assertions.assertEquals(lxf { (litInt(13) lt c) and eq(litInt(13), litInt(14)) }, simplifier.simplify(f1))
    }

    @Test
    fun testSimplifyMultiple() {
        // doubly nested cases
        val f1 = lxf {
            exists(x, y) { eq(x, litInt(13)) and eq(y, litInt(14)) and (x lt y) }
        }
        Assertions.assertEquals(lxf { litInt(13) lt litInt(14) }, simplifier.simplify(f1))

        val f2 = lxf {
            forall(x, y) { !eq(x, litInt(13)) or !eq(y, litInt(14)) or (x lt y) }
        }
        Assertions.assertEquals(lxf { litInt(13) lt litInt(14) }, simplifier.simplify(f2))

        // alternating cases
        val f3 = lxf {
            forall(x) { !eq(x, litInt(13)) or exists(y) { eq(y, litInt(14)) and (x lt y) } }
        }
        Assertions.assertEquals(lxf { litInt(13) lt litInt(14) }, simplifier.simplify(f3))

        val f4 = lxf {
            exists(x) { eq(x, litInt(13)) and forall(y) { !eq(y, litInt(14)) or (x lt y) } }
        }
        Assertions.assertEquals(lxf { litInt(13) lt litInt(14) }, simplifier.simplify(f4))

        // doubly nested plus useless variable cases
        val f5 = lxf {
            exists(x, y, z) { eq(x, litInt(13)) and eq(y, litInt(14)) and (x lt y) }
        }
        Assertions.assertEquals(lxf { litInt(13) lt litInt(14) }, simplifier.simplify(f5))

        val f6 = lxf {
            forall(z, x, y) { !eq(x, litInt(13)) or !eq(y, litInt(14)) or (x lt y) }
        }
        Assertions.assertEquals(lxf { litInt(13) lt litInt(14) }, simplifier.simplify(f6))

        // doubly nested der plus some non-eliminatable variable
        val f7 = lxf {
            exists(x, y, z) { eq(x, litInt(13)) and eq(y, litInt(14)) and (x lt y) and (x lt z) }
        }
        Assertions.assertEquals(lxf { exists(z) { (litInt(13) lt litInt(14)) and (litInt(13) lt z) } }, simplifier.simplify(f7))

        val f8 = lxf {
            forall(z, x, y) { !eq(x, litInt(13)) or !eq(y, litInt(14)) or (x lt y) or (x lt z) }
        }
        Assertions.assertEquals(lxf { forall(z) { (litInt(13) lt litInt(14)) or (litInt(13) lt z) } }, simplifier.simplify(f8))
    }


}
