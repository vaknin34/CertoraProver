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

package scene.source

import bridge.ContractInstanceInSDC
import compiler.AbstractSolcRunner
import config.Config
import utils.ArtifactFileUtils

class SolidityContractSource(filename: String) : IContractSourceFull {

    private val solcRunner = object : AbstractSolcRunner() {
        override fun getContractSource(): Map<String, Source> =
            mapOf(
                (Config.SubContract.getOrNull() ?: ArtifactFileUtils.getBasenameOnly(filename)) to
                        Source.FromFile(
                            filename
                        )
            )

        override fun getSolcExecutable(): String =
            Config.Solc.get()

        override fun getAllowedPaths(): List<String> = listOf(Config.SolcAllowedPath.getOrNull()).mapNotNull { it }

    }

    override fun instances(): List<ContractInstanceInSDC> =
        solcRunner.contractInstances

    override fun fullInstances(): List<ContractInstanceInSDC> = instances()

}
