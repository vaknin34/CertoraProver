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

import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import vc.data.TACExprFactUntyped

object TACExprPrettyPrinterTest {

    private val pp = TACExprPrettyPrinter
    private val txf = TACExprFactUntyped

    @Test
    fun exp01() {
        val res = pp.print(txf {
            Ite(
                Eq(
                    number(0),
                    number(1),
                ),
                Ite(
                    Gt(
                        number(2),
                        number(3),
                    ),
                    number(4),
                    number(5),
                ),
                number(6),
            )
        })
        println(res)
        assertTrue("==" in res)
        assertTrue("Ite" in res)
    }

}
