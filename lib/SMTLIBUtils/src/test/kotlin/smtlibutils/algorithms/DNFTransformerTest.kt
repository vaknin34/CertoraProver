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
import smtlibutils.data.*
import smtlibutils.parser.SMTParser

internal class DNFTransformerTest: WithResourceFile {
    @Test
    fun DNFTest01() {
        val script = SharingSmtScript()
        val parser = SMTParser(loadResourceFileOrCrash("dnftransformer/dnfTransformerTest01.smt2"))
        parser.parse(script)
        val smt = parser.getSmt()
        val sortedSmt = Sorter(script).smt(smt)

        val smtScript = FactorySmtScript

        val asserts = sortedSmt.cmds.filterIsInstance<Cmd.Assert>()

        var ctr = 0
        while (ctr < asserts.size - 1) {
            println("dnf-transforming ${sortedSmt.cmds[ctr]}")
            assertTrue(DNFTransformer.transformToDNF(asserts[ctr].e).toExp(smtScript) == asserts[ctr + 1].e)
            ctr += 2
        }
    }
}
