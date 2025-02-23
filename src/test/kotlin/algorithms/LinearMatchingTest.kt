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

package algorithms

import analysis.numeric.linear.*
import analysis.numeric.linear.TermMatching.matches
import com.certora.collect.*
import datastructures.stdcollections.*
import org.jetbrains.annotations.TestOnly
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import tac.Tag
import vc.data.TACSymbol
import java.math.BigInteger


class LinearMatchingTest {
    private val v1 = TACSymbol.Var("v1", Tag.Bit256)
    private val v2 = TACSymbol.Var("v2", Tag.Bit256)
    private val v3 = TACSymbol.Var("v3", Tag.Bit256)
    private val v4 = TACSymbol.Var("v4", Tag.Bit256)


    sealed class MatchDef {
        data class SymMatch(val nm: String, val sym: LVar.PVar) : MatchDef()
        data class ValueMatch(val nm: String, val c: BigInteger) : MatchDef()
    }

    interface MatchSpecClosure {
        fun TermMatching.Match.check(d: MatchDef) = when(d) {
            is MatchDef.ValueMatch -> {
                Assertions.assertTrue(d.nm in this.factors, "No match for value wildcard ${d.nm}")
                Assertions.assertEquals(d.c, this.factors[d.nm]!!, "Mismatch for value wildcard ${d.nm}")
            }
            is MatchDef.SymMatch -> {
                Assertions.assertTrue(d.nm in this.symbols, "No match for symbol wildcard ${d.nm}")
                Assertions.assertEquals(d.sym, this.symbols[d.nm], "Mismatch for symbol wildcard ${d.nm}")
            }
        }

        infix fun String.isBoundTo(v: TACSymbol.Var)
        infix fun String.isBoundTo(c: BigInteger)
        infix fun String.isBoundTo(k: Int)
    }



    class Expecting(private val wrapped: LinearInvariants, private val builder: TermMatching.Builder.() -> TermMatching.Builder.Term) {
        infix fun expecting(f:  MatchSpecClosure.() -> Unit) : TermMatching.Match {
            val match = wrapped.matches(builder).singleOrNull()
            Assertions.assertNotNull(match, "Match failed")
            object : MatchSpecClosure {
                override fun String.isBoundTo(v: TACSymbol.Var) {
                    match!!.check(MatchDef.SymMatch(this, LVar.PVar(v)))
                }

                override fun String.isBoundTo(c: BigInteger) {
                    match!!.check(MatchDef.ValueMatch(this, c))
                }

                override fun String.isBoundTo(k: Int) {
                    this isBoundTo k.toBigInteger()
                }
            }.f()
            return match!!
        }
    }

    class ForMatch(private val wrapped: LinearInvariants) {
        infix fun against(other: TermMatching.Builder.() -> TermMatching.Builder.Term) : Expecting = Expecting(wrapped, other)
        infix fun failsOn(other: TermMatching.Builder.() -> TermMatching.Builder.Term) {
            Assertions.assertTrue(wrapped.matches(other).isEmpty(), "Matched when it should not have")
        }
    }



    @TestOnly
    fun match(f: LinearEquality.Builder.() -> LinearEquality) : ForMatch {
        return ForMatch(treapSetOf((object : LinearEquality.Builder {
            override val `1`: BigInteger
                get() = BigInteger.ONE
            override val `0`: BigInteger
                get() = BigInteger.ZERO
            override val `-1`: BigInteger
                get() = `1`.negate()
        }).f()))
    }

    @Test
    fun testMatchFailures() {
        match {
            !v1 `=` !v2
        } failsOn {
            v("tmp") * 2 `=` v("tmp2")
        }

        match {
            !v1 `=` !v2
        } failsOn {
            v("tmp") - v("v2") `=` k("non-zero") {
                it > BigInteger.ZERO
            }
        }
    }

    @Test
    fun testBasicMatching() {
        match {
            !v1 `=` !v2
        } against {
            v1 `=` v("which")
        } expecting {
            "which" isBoundTo v2
        }

        match {
            !v1 `=` !v2 + 3
        } against {
            v1 `=` v("which") + 3
        } expecting {
            "which" isBoundTo v2
        }

        match {
            !v1 `=` !v2 + 3
        } against {
            v1 - k("sub") `=` v("which")
        } expecting {
            "which" isBoundTo v2
            "sub" isBoundTo 3
        }

        match {
            !v1 `=` ((!v2 * 10 - !v3 * 10) + !v4)
        } against {
            v1 `=` (v("v2") * n("k2") - v("v3") * k("k3")) * 2 + v("v4")
        } expecting {
            "v2" isBoundTo v2
            "v3" isBoundTo v3
            "k2" isBoundTo 5
            "k3" isBoundTo 5
            "v4" isBoundTo v4
        }

        match {
            !v1 * 6 `=` (!v2 - !v3) + !v4 * 6
        } against {
            v1 * k("f1") `=` (v2 - v3) + v4 * k("f2") + k("zero")
        } expecting {
            "f1" isBoundTo 6
            "f2" isBoundTo 6
            "zero" isBoundTo 0
        }
    }
}
