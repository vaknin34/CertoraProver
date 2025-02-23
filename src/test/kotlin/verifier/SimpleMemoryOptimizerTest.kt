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

package verifier

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import vc.data.TACBuilderAuxiliaries
import vc.data.TACCmd
import vc.data.TACProgramBuilder


class SimpleMemoryOptimizerTest : TACBuilderAuxiliaries() {

    @Test
    fun simpleMemoryOptimizerTest() {
        val originalProg = TACProgramBuilder {
            mkBmVar("a_1").byteStore(intConst(0), bv256Var("b_1")) // this should be dropped by the optimization
            mkBmVar("c_1").byteStore(intConst(0), bv256Var("d_1"))
            boolVar("some_bool") assign (mkBmVar("c_1").asSym() eq mkBmVar("c_1").asSym())
            assert(boolVar("some_bool"))
        }

        val newProg = SimpleMemoryOptimizer.removeUnusedWrites(originalProg.code)

        val expectedProg = TACProgramBuilder {
            addCmd(TACCmd.Simple.NopCmd)
            mkBmVar("c_1").byteStore(intConst(0), bv256Var("d_1"))
            boolVar("some_bool") assign (mkBmVar("c_1").asSym() eq mkBmVar("c_1").asSym())
            assert(boolVar("some_bool"))
        }

        assertEquals(expectedProg.code.digest(), newProg.digest())
    }

    @Test
    fun dropLogsMemoryOptimizerTest() {
        val originalProg = TACProgramBuilder {
            mkBmVar("a_1").byteStore(intConst(0), bv256Var("b_1")) // this should be dropped by the optimization
            mkBmVar("c_1").byteStore(intConst(0), bv256Var("d_1"))
            boolVar("some_bool") assign (mkBmVar("c_1").asSym() eq mkBmVar("c_1").asSym())
            // this should not make "a_1" live
            addCmd(TACCmd.Simple.LogCmd(listOf(mkBmVar("a_1"))))
            assert(boolVar("some_bool"))
        }

        val newProg = SimpleMemoryOptimizer.removeUnusedWrites(originalProg.code)

        val expectedProg = TACProgramBuilder {
            addCmd(TACCmd.Simple.NopCmd)
            mkBmVar("c_1").byteStore(intConst(0), bv256Var("d_1"))
            boolVar("some_bool") assign (mkBmVar("c_1").asSym() eq mkBmVar("c_1").asSym())
            addCmd(TACCmd.Simple.LogCmd(listOf(mkBmVar("a_1"))))
            assert(boolVar("some_bool"))
        }

        assertEquals(expectedProg.code.digest(), newProg.digest())
    }
}
