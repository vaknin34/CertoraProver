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

package analysis.split

import org.junit.jupiter.api.Test
import spec.cvlast.typedescriptors.EVMTypeDescriptor
import vc.data.*
import vc.data.TACMeta.BIT_WIDTH
import vc.data.TACMeta.STORAGE_TYPE

internal class StorageTypeBounderTest : TACBuilderAuxiliaries() {

    private fun optimize(
        prog: TACProgramBuilder.BuiltTACProgram,
    ) {
        val contract = mockContract(prog.code)
        val optimizer = StorageTypeBounder(contract)
        optimizer.addBounds()
            // return contract.methods.values.single().code as CoreTACProgram
    }

    private fun TACSymbol.Var.signed(width: Int) =
        this.withMeta(STORAGE_TYPE, EVMTypeDescriptor.IntK(width))
            .withMeta(BIT_WIDTH, width)

    @Test
    fun analysis1() {
        val prog = TACProgramBuilder {
            b assign BWAnd(aS, 0xff.asTACExpr)
            g assign b
            c.signed(8) assign g
            nop
            d assign c.signed(8)
            e assign d
            f assign SignExtend(0.asTACExpr, eS)
        }
        optimize(prog)
    }


    @Test
    fun analysis2() {
        val map = wordMapVar("map").signed(8)
        val prog = TACProgramBuilder {
            map[3.asTACSymbol()] assign 0xfe.asTACSymbol()
            jump {
                b assign BWAnd(aS, 0xff.asTACExpr)
                map[1.asTACSymbol()] assign b
            }
            jump {
                d assign map[3.asTACSymbol()]
                e assign d
                f assign SignExtend(0.asTACExpr, eS)
            }
        }
        optimize(prog)
    }
}
