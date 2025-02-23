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

package vc.data.tacexprutil

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder
import vc.data.asTACExpr

class CmdsFolderTest : TACBuilderAuxiliaries() {

    @Test
    fun testFolding() {
        val prog = TACProgramBuilder {
            b assign Mul(aS, 10.asTACExpr)
            d assign Div(BWAnd(bS, 0xff.asTACExpr), aS)
            z assign Eq(dS, 10.asTACExpr)
        }
        val cmds = prog.code.analysisCache.graph.blocks.first().commands.map { it.cmd }
        Assertions.assertEquals(
            txf {
                Eq(Div(BWAnd(Mul(aS, 10.asTACExpr), 0xff.asTACExpr), aS), 10.asTACExpr)
            },
            CmdsFolder.fold(zS, cmds)
        )
    }


    @Test
    fun testReuseOfSubexpressions() {
        val prog = TACProgramBuilder {
            b assign Add(cS, cS)
            a assign Add(bS, bS)
            z assign Eq(aS, aS)
        }
        val cmds = prog.code.analysisCache.graph.blocks.first().commands.map { it.cmd }
        val resExpr = CmdsFolder.fold(zS, cmds)!!
        // Actually there should only be 4 distinct sub-expressions. However, for some reason `cS` is two distinct
        // expressions already in the original program. Couldn't follow why exactly.
        assertTrue(resExpr.subs.groupBy { System.identityHashCode(it) }.size <= 5)
    }
}
