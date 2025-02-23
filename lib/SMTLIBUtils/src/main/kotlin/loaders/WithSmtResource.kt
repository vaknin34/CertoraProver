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

package loaders

import smtlibutils.data.SMT
import smtlibutils.data.SmtScript
import smtlibutils.data.Sorter
import smtlibutils.parser.SMTParser

interface WithSmtResource: WithResourceFile {
    /**
     * @param filePath needs to relative to classpath (e.g. test..resources directory)
     */
    fun loadSmtScriptResource(filePath: String, script: SmtScript) : SMT {
        val parser = SMTParser(loadResourceFileOrCrash(filePath))
        parser.parse(script)
        val smt = parser.getSmt()
        return Sorter(script).smt(smt)
    }
}