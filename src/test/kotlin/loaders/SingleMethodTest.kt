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

import analysis.TACCommandGraph
import org.junit.jupiter.api.Assertions
import scene.ITACMethod
import spec.cvlast.SolidityContract
import vc.data.CoreTACProgram

interface SingleMethodTest : SceneTest {
    fun loadTestMethod(src: String, solc: String = "solc", optimize: Boolean) : ITACMethod {
        val scene = getTestScene(src, solc, optimize)
        return scene.getContract(SolidityContract("Test")).getMethods().firstOrNull {
            it.name == "test"
        } ?: Assertions.fail { "Failed to find method test in contract Test" }
    }

    fun loadTestGraph(src: String, solc: String = "solc", optimize: Boolean) : TACCommandGraph {
        return loadTestMethod(src, solc, optimize).let {
            TACCommandGraph(it.code as CoreTACProgram)
        }
    }
}
