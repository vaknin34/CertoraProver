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

import analysis.PTARunPurpose
import analysis.PointerAnalysis
import analysis.TACCommandGraph
import bridge.ContractInstanceInSDC
import decompiler.Decompiler
import decompiler.Disassembler
import disassembler.DisassembledEVMBytecode
import org.junit.jupiter.api.Assertions
import scene.ITACMethod
import scene.TrivialContractCache
import testing.StaticContractSource
import vc.data.CoreTACProgram
import verifier.ContractUtils
import java.math.BigInteger

interface SolidityContractTest : WithResourceFile, SingleMethodTest {
    fun loadTestContractMethod(path: String, solc: String, optimize: Boolean): ITACMethod {
        val src = this.loadResourceFile(path)
        Assertions.assertNotNull(src) {
            "Contract source $path not found"
        }
        return this.loadTestMethod(src!!, solc, optimize)
    }

    fun loadTestContractGraph(path: String, solc: String, optimize: Boolean) : TACCommandGraph {
        return this.loadTestContractMethod(path, solc, optimize).let {
            TACCommandGraph(it.code as CoreTACProgram)
        }
    }

    fun getDecompiledResultFromInstance(
        instance: ContractInstanceInSDC,
        disassembledCode: DisassembledEVMBytecode
    ): ContractUtils.SimplifiedDecompiledContract {
        val decompiledCode = Decompiler.decompileEVM(
            disassembledCode,
            instance
        )

        return ContractUtils.SimplifiedDecompiledContract(decompiledCode, TrivialContractCache)
    }

    fun loadDecompiled(src: String, solc: String = "solc", optimize: Boolean = false) : ContractUtils.SimplifiedDecompiledContract {
        val sceneSource = StaticContractSource(src, solc, BigInteger.ZERO, optimize)
        Assertions.assertEquals(0, sceneSource.runnerErrors.size) {
            "Compilation of test source failed with errors ${sceneSource.runnerErrors}"
        }
        Assertions.assertEquals(1, sceneSource.instances().size)
        val instance = sceneSource.instances().single()
        return getDecompiledResultFromInstance(
            instance,
            Disassembler.disassembleRuntimeBytecode(instance)
        )
    }

}

fun runPTA(method: ITACMethod) = PointerAnalysis.runAnalysis(method, PTARunPurpose.TEST)
