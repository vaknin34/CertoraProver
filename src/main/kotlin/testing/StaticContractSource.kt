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

package testing

import bridge.ContractInstanceInSDC
import compiler.AbstractSolcRunner
import org.apache.commons.lang3.SystemUtils
import scene.source.IContractSourceFull
import java.math.BigInteger

class StaticContractSource(val sourceCode: String, private val solidityExec : String = "solc", address: BigInteger = BigInteger.ZERO, optimize: Boolean) : IContractSourceFull {
    private val runner = object : AbstractSolcRunner(address, optimize) {
        override fun getContractSource(): Map<String, Source> =
                mapOf("test" to Source.Literal(contractSource = sourceCode))
        override fun getSolcExecutable(): String = "${solidityExec}${if (SystemUtils.IS_OS_WINDOWS) ".exe" else ""}"
    }

    val runnerErrors : List<String> get() = runner.errors

    override fun instances(): List<ContractInstanceInSDC> = runner.contractInstances

    override fun fullInstances(): List<ContractInstanceInSDC> = instances()
}
