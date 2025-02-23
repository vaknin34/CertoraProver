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

import smtlibutils.data.Cmd
import utils.*

/**
 * This class provides a simple utility to safely manage and restore the context, i.e. SMT-LIB's push and pop commands,
 * of a query processor. It solves the issue of utilities not properly cleaning up (i.e. calling pop), for example due
 * to exceptions. Given that all push and pop commands are issued through this context class, it closes all remaining
 * scopes since its construction when the context object is closed.
 *
 * The intended usage is roughly as follows:
 * SmtQueryProcessorContext(queryProcessor).use { context -> <code> }
 * where `<code>` uses the queryProcessor as usual except for calling push() and pop() on `context` instead of on the
 * `queryProcessor` directly.
 */
class SmtQueryProcessorContext(private val queryProcessor: SmtQueryProcessor) : SuspendCloseable{
    private var openScopes: Int = 0

    /** Invoke queryProcessor.push() */
    suspend fun push(comment: String? = null) {
        openScopes += 1
        queryProcessor.push(Cmd.Push(1, comment))
    }

    /** Invoke queryProcessor.pop() */
    suspend fun pop(comment: String? = null) {
        queryProcessor.pop(Cmd.Pop(1, comment))
        openScopes -= 1
    }

    /** Close all remaining scopes. */
    override suspend fun close() {
        queryProcessor.pop(Cmd.Pop(openScopes, "reset scopes"))
    }
}
