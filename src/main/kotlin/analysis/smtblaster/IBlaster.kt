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

package analysis.smtblaster

import smtlibutils.data.Cmd

interface IBlaster {
    fun blastSmt(vc_query: List<Cmd>) : Boolean {
        return blastSmtOrTimeout(vc_query).first
    }
    fun blastSmtOrTimeout(vc_query: List<Cmd>) : Pair<Boolean, Boolean>

    companion object {
        var FAIL_ON_TIMEOUT: Boolean = false
        var FAIL_ON_SMT_ERROR: Boolean = true
        const val BLASTERS_SUBDIR_NAME = "blasters"
    }

    class SmtTimeoutError : Error()

    class SMTError(z3output : String) : Error(z3output)
}
