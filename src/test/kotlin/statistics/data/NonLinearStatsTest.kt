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

package statistics.data

import algorithms.SimpleDominanceAnalysis
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder

class NonLinearStatsTest: TACBuilderAuxiliaries() {

    val i0 = intVar("i0")
    val i1 = intVar("i1")
    val i2 = intVar("i2")
    val i3 = intVar("i3")
    val i4 = intVar("i4")

    val i0S = i0.asSym()
    val i1S = i1.asSym()
    val i2S = i2.asSym()
    val i3S = i3.asSym()
    val i4S = i4.asSym()


    @Test
    fun t1() {
        val prog = TACProgramBuilder {
            i assign IntMul(jS, kS)
            x assign Lt(iS, number(10))
            assert(x)
        }.code

        val stats = NonLinearStats.compute(prog, emptyMap(), doDataFlowAnalysis = true)

        assertEquals(2, stats.highestDegree)
    }


    @Test
    fun t2() {
        val prog = TACProgramBuilder {
            jumpCond(x)
            jump {
                i assign IntMul(jS, kS)
                jump(1) {
                    x assign Lt(iS, number(10))
                    assert(x)
                }
            }
            jump {
                i assign 2
                jump(1)
            }
        }.code

        val stats = NonLinearStats.compute(prog, emptyMap(), doDataFlowAnalysis = true)

        assertEquals(2, stats.highestDegree)
    }

    @Test
    fun t3() {
        val prog = TACProgramBuilder {
            jumpCond(x)
            jump {
                i assign IntMul(IntMul(jS, kS), i0S)
                jump(1) {
                    x assign Lt(iS, number(10))
                    assert(x)
                }
            }
            jump {
                i assign 2
                jump(1)
            }
        }.code

        val stats = NonLinearStats.compute(prog, emptyMap(), doDataFlowAnalysis = true)

        assertEquals(3, stats.highestDegree)
    }

    @Test
    fun t4() {
        val prog = TACProgramBuilder {
            jumpCond(x)
            jump {
                i assign IntMul(jS, kS) // i -> 2
                jump(1) {
                    x assign Lt(iS, number(10)) // i -> 3
                    assumeExp(IntMul(iS, iS) eq number(100)) // i * i -> 6
                    assert(x)
                }
            }
            jump {
                i assign IntMul(IntMul(jS, kS), i0S) // i -> 3
                jump(1)
            }
        }.code

        val stats = NonLinearStats.compute(prog, emptyMap(), doDataFlowAnalysis = true)

        assertEquals(6, stats.highestDegree)
    }


    /** We use this in DSA context only so far -- but the algorithm shouldn't care.. */
    @Test
    fun worksEvenWithoutDsa() {
        val prog = TACProgramBuilder {
            jumpCond(x)
            jump {
                i assign IntMul(jS, kS) // i -> 2
                jump(1) {
                    x assign Lt(iS, number(10)) // i -> 6
                    assumeExp(IntMul(iS, iS) eq number(100)) // i * i -> 12
                    assert(x)
                }
            }
            jump {
                i assign IntMul(IntMul(jS, kS), i0S) // i -> 3
                i assign IntMul(iS, iS) // i -> 6 (it should also work if there's no DSA, right)
                jump(1)
            }
        }.code

        val stats = NonLinearStats.compute(prog, emptyMap(), doDataFlowAnalysis = true)

        assertEquals(12, stats.highestDegree)
    }

    /**
     *
     * R607 = tacCalldatabufCANON1@6*R605
     * R608 = R607/tacCalldatabufCANON1@6
     * R612 = (R286==0x0)||(R608==R605) ? 0x1 : 0x0
     * R615 = !(CANON32!!27==0x0) ? 0x1 : 0x0
     * R616 = R615&R612
     * assume R616>0x0
     * R618 = R607/CANON32!!27
     */
    @Test
    fun fromERC4626Redeem() {
        val (_, cdbfs) = "cdbfs".bvVarAndSym
        val (_, cnns) = "cnns".bvVarAndSym
        val (_, R286s) = "R286".bvVarAndSym
        val (R607, R607s) = "R607".bvVarAndSym
        val (R605, R605s) = "R605".bvVarAndSym
        val (R608, R608s) = "R608".bvVarAndSym
        val (R612, R612s) = "R612".bvVarAndSym
        val (R615, R615s) = "R615".bvVarAndSym
        val (R616, R616s) = "R616".bvVarAndSym
        val (R618, _) = "R618".bvVarAndSym

        val prog = TACProgramBuilder {
            R605 assign BWAnd(aS, bS) // represents an expression that is assigned, but from something the analysis does not understand
            R607 assign Mul(cdbfs, R605s)
            R608 assign Div(R607s, cdbfs) // 608 ~~> 3
            R612 assign Ite(
                            LOr(
                                (R286s eq number(0)),
                                (R608s eq R605s)
                            ),
                            number(1),
                            number(0)
                        )
            R615 assign Ite(LNot(cnns eq number(0)), number(1), number(0))
            R616 assign BWAnd(R615s, R612s)
            assumeExp(Gt(R616s, number(0x0)))
            R618 assign Div(R607s, cnns) // 618 ~~> 3
            assert(true)
        }.code

        NonLinearStats.compute(
            prog,
            emptyMap(),
            doDataFlowAnalysis = true,
            divAndModSum = true
        ).let { stats ->
            assertEquals(3, stats.highestDegree)
        }
        NonLinearStats.compute(
            prog,
            emptyMap(),
            doDataFlowAnalysis = true,
            divAndModSum = false,
        ).let { stats ->
            assertEquals(2, stats.highestDegree)
        }
    }

    /**
     * We're tracking flow through memory.
     * (We use a broad "may equals" assumption for all array accesses here.)
     */
    @Test
    fun throughMemory() {
        val (_, m0S) = "m0".bmVarAndSym
        val (m1, m1S) = "m1".bmVarAndSym
        val prog = TACProgramBuilder {
            a assign Mul(bS, cS)
            m1 assign Store(m0S, dS, v = aS)
            e assign Select(m1S, gS) // we assume d and g may alias (no matter the existing constraints)
            g assign Mul(eS, fS)
            x assign Lt(gS, number(10))
            assert(x)
        }.code

        NonLinearStats.compute(
            prog = prog,
            callIdNames = emptyMap(),
            doDataFlowAnalysis = true,
            dataFlowsThroughMaps = true,
        ).let { stats ->
            assertEquals(3, stats.highestDegree)
        }
        NonLinearStats.compute(
            prog = prog,
            callIdNames = emptyMap(),
            doDataFlowAnalysis = true,
            dataFlowsThroughMaps = false,
        ).let { stats ->
            assertEquals(2, stats.highestDegree)
        }
    }

    /**
     * Example illustrating how the polynomial degree can be exponential in the number of commands in the program.
     * (Slightly academic, perhaps banal to some, but I want to document the phenomenon .. it does happen in practice..)
     */
    @Test
    fun exponentialPolyDeg() {
        val prog = TACProgramBuilder {
            i assign IntMul(iS, iS) // i -> 2
            i assign IntMul(iS, iS) // i -> 4
            i assign IntMul(iS, iS) // i -> 8
            i assign IntMul(iS, iS) // i -> 16
        }.code
        NonLinearStats.compute(
            prog = prog,
            callIdNames = emptyMap(),
            doDataFlowAnalysis = true,
            dataFlowsThroughMaps = true,
        ).let { stats ->
            assertEquals(4, stats.numberOfNonlinearOps)
            assertEquals(16, stats.highestDegree)
        }
    }

    /**
     * Build a large synthetic program and run on it, as a performance test for the analysis.
     * The program is a sequence of diamonds, each basic block does a nonlinear operation.
     * Each diamond looks like this:
     * ```
     * if (b)
     *   i = i * j
     * else
     *   i = i * k
     * ```
     * The expected polynomial degree is "nrDiamonds + 1". The expected number of nonlinear operations is
     * "2 * nrDiamonds".
     *
     * The current bottleneck is [SimpleDominanceAnalysis], setting the number of diamonds to 5000 will show it runs
     * for more than 10 secs. So this is kept here till we find the time to optimize it.
     */
    @Test
    fun performance01() {
        val nrDiamonds = 4
        val prog = TACProgramBuilder {
            havoc(i) // just so the start block is not empty
            jump(1)
            (1 .. nrDiamonds).forEach { idx ->
                jumpDest(idx) {
                    jumpCond(x)
                    jump {
                        i assign IntMul(iS, jS)
                        jump(idx + 1)
                    }
                    jump {
                        i assign IntMul(iS, kS)
                        jump(idx + 1)
                    }
                }
            }
            jumpDest(nrDiamonds + 1) {
                x assign Lt(iS, number(10)) // no actual meaning, just to use the contents of `i`
            }
        }.code
        NonLinearStats.compute(
            prog = prog,
            callIdNames = emptyMap(),
            doDataFlowAnalysis = true,
        ).let { stats ->
            assertEquals(nrDiamonds * 2, stats.numberOfNonlinearOps)
            assertEquals(nrDiamonds + 1, stats.highestDegree)
        }
    }
}
