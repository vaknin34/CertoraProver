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

import org.junit.jupiter.api.Assertions
import scene.IScene
import scene.SceneFactory
import scene.loader.SimpleProverContractLoader
import testing.StaticContractSource
import java.math.BigInteger

interface SceneTest {
    fun getTestScene(src: String, solc: String, optimize: Boolean, address: BigInteger = BigInteger.ZERO): IScene {
        val sceneSource = StaticContractSource(src, solc, address, optimize)
        Assertions.assertEquals(0, sceneSource.runnerErrors.size) {
            "Compilation of test source failed with errors ${sceneSource.runnerErrors}"
        }
        return SceneFactory.getScene(sceneSource, SimpleProverContractLoader)
    }
}
