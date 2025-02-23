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
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import smtlibutils.data.Cmd
import smtlibutils.data.SharingSmtScript
import smtlibutils.data.Sorter
import smtlibutils.parser.SMTParser

internal class NNFTransformerTest: WithResourceFile {
    @Test
    fun NNFTest01() {
        val script = SharingSmtScript()
        val parser = SMTParser(loadResourceFileOrCrash("nnftransformer/nnfTest01.smt2"))
        parser.parse(script)
        val smt = parser.getSmt()
        val sortedSmt = Sorter(script).smt(smt)

        var ctr = sortedSmt.cmds.indexOf(sortedSmt.cmds.find { it is Cmd.Assert })
        while (ctr < sortedSmt.cmds.size - 1) {
            println("nnf-transforming ${sortedSmt.cmds[ctr]}")
            assertTrue(NNFTransformer().cmd(sortedSmt.cmds[ctr]) == sortedSmt.cmds[ctr + 1])
            ctr += 2
        }
    }
}
