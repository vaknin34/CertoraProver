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

package smtlibutils.algorithms

import loaders.WithResourceFile
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import smtlibutils.data.Cmd
import smtlibutils.data.SharingSmtScript
import smtlibutils.data.Sorter
import smtlibutils.parser.SMTParser

internal class IteEliminatorTest: WithResourceFile {
    @Test
    fun iteEliminatorTest01() {
        val script = SharingSmtScript()
        val parser = SMTParser(loadResourceFileOrCrash("iteeliminator/iteElimTest01.smt2"))
        parser.parse(script)
        val smt = parser.getSmt()
        val sortedSmt = Sorter(script).smt(smt)

        val asserts = sortedSmt.cmds.filterIsInstance<Cmd.Assert>()

        var ctr = 0
        while (ctr < asserts.size - 2) {
            println("ite-eliminating ${asserts[ctr]}")
            Assertions.assertTrue(IteEliminator.eliminateAllIte(asserts[ctr].e, IteEliminator.Mode.CONJUNCTION) ==
                    asserts[ctr + 1].e)
            Assertions.assertTrue(IteEliminator.eliminateAllIte(asserts[ctr].e, IteEliminator.Mode.DISJUNCTION) ==
                    asserts[ctr + 2].e)
            ctr += 3
        }
    }
}
