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

package rules.genericrulecheckers.msgvalueinloop

import bridge.NamedContractIdentifier
import loaders.WithTACSource
import org.junit.jupiter.api.Assertions
import scene.ITACMethod
import scene.Scene

object GenericRuleTestUtils {
        fun getMethod(scene: Scene, contractName: NamedContractIdentifier, functionName: String): ITACMethod {
        val m = scene.getContractOrNull(contractName)?.getMethods()?.firstOrNull {
            it.name == functionName
        } ?: Assertions.fail(
            "Could not find Test-$functionName in ${contractName.name}"
        )
        return m
    }
}
