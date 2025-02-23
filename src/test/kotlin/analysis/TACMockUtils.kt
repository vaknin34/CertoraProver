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

package analysis

import org.junit.jupiter.api.Assertions
import testing.ttl.MOCK_TAG
import utils.firstMapped

object TACMockUtils {
    fun commandWithTagOrFail(graph: TACCommandGraph, v: String): CmdPointer {
        return commandWithTag(graph, v) ?: Assertions.fail {
            "Did not find command with tag $v"
        }
    }

    private fun commandWithTag(graph: TACCommandGraph, v: String): CmdPointer? {
        return graph.commands.asIterable().firstMapped {
            if (it.cmd.meta.get(MOCK_TAG) == v) {
                it.ptr
            } else {
                null
            }
        }
    }
}