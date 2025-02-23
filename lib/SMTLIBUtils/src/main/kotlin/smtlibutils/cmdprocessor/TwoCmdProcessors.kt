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

package smtlibutils.cmdprocessor

import kotlinx.coroutines.flow.*
import smtlibutils.data.Cmd
import utils.*

class TwoCmdProcessors(val first: CmdProcessor, val second: CmdProcessor) : CmdProcessor {
    override val solverInstanceInfo: SolverInstanceInfo
        get() = listOf(first, second).map { it.solverInstanceInfo }.reduce(SolverInstanceInfo.Companion::reduce)
    override val options: CmdProcessor.Options
        get() = listOf(first, second).map { it.options }.reduce(CmdProcessor.Options.Companion::reduceOptions)

    override fun processResult(cmd: Cmd): Flow<String> {
        return first.processResult(cmd) + second.processResult(cmd)
    }

    override fun close() {
        first.close()
        second.close()
    }

    override fun checkSat(comment: String?): Flow<String> {
        return first.checkSat(comment) + second.checkSat(comment)
    }

    override suspend fun reset(comment: String?) {
        first.reset(comment)
        second.reset(comment)
    }
}
