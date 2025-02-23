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

package infra

import infra.CertoraBuild.Companion.EVMCompiler
import infra.CertoraBuild.Companion.solcOptimize
import infra.CertoraBuild.Companion.viaIR
import infra.CertoraBuildSource.TempDirWithGeneratedContract
import io.mockk.mockk
import kotlinx.serialization.json.JsonObjectBuilder
import report.ReporterContainer
import report.TreeViewReporter
import rules.ICheckableTAC
import scene.IScene
import scene.ProverQuery
import scene.SceneFactory
import scene.SceneType
import spec.converters.EVMMoveSemantics
import spec.cvlast.typechecker.CVLError
import spec.cvlast.typedescriptors.EVMTypeDescriptor
import spec.cvlast.typedescriptors.theSemantics
import utils.*
import utils.CertoraFileCache.certoraSourcesDir
import utils.CollectingResult.Companion.map
import vc.data.CoreTACProgram
import verifier.IntegrativeChecker
import java.nio.file.Path
import kotlin.io.path.nameWithoutExtension

class CVLFlow {
    fun getProverQuery(confPath: Path): CollectingResult<ProverQuery, CVLError> {
        return CertoraBuild
            .inTempDir(CertoraBuildKind.EVMBuild(), confPath)
            .use { build -> build.getProverQueryFromVerificationQuery() }
    }


    fun getProverQueryWithScene(
        contract: String,
        solc: String,
        withOptimize: Boolean,
        cvlText: String,
        viaIR: Boolean = false,
        primaryContractName: String = "test",
    ) = getProverQueryWithScene(
        primaryContractName = primaryContractName,
        contract = contract,
        cvlText = cvlText,
        compiler = EVMCompiler.Solidity(solc),
        buildConf = {
            solcOptimize(withOptimize)
            viaIR(viaIR)
        }
    )

    /**
     * this function:
     * 1. creates in [workingDirectory] and in [certoraSourcesDir], a temporary CVL file with the contents of [contract]
     * 2. creates in [workingDirectory], a temporary conf file generated from parameters passed
     * 3. uses these files to call [getProverQueryWithScene]
     *
     * files created here are temporary and will be auto-deleted.
     */
    fun getProverQueryWithScene(
        primaryContractName: String = "test",
        contract: String,
        cvlText: String,
        compiler: EVMCompiler,
        buildConf : JsonObjectBuilder.() -> Unit = {}
    ): CollectingResult<Pair<IScene, ProverQuery>, CVLError> {
        return CertoraBuild
            .withGeneratedContract(primaryContractName, contract, compiler, buildConf)
            .use { build ->
                val contractName = when(compiler) {
                    is EVMCompiler.Solidity -> primaryContractName
                    is EVMCompiler.Vyper -> (build.source as TempDirWithGeneratedContract).contract.nameWithoutExtension
                }
                build.getProverQueryWithSceneFromText(cvlText, contractName)
            }
    }

    fun getProverQuery(
        confPath: Path,
        cvlText: String,
        primaryContractName: String
    ): CollectingResult<ProverQuery, CVLError> {
        return getProverQueryWithScene(confPath, cvlText, primaryContractName).map { it.second }
    }

    /** [confPath] is the path to the run's .conf file, either absolute or relative to the cwd */
    fun getProverQueryWithScene(
        confPath: Path,
        cvlText: String,
        primaryContractName: String
    ): CollectingResult<Pair<IScene, ProverQuery>, CVLError> {
        return CertoraBuild
            .inTempDir(CertoraBuildKind.EVMBuild(), confPath)
            .use { build -> build.getProverQueryWithSceneFromText(cvlText, primaryContractName) }
    }

    private fun treeViewReporterDummyMock(): TreeViewReporter = mockk(relaxed = true)

    /**
     * Transforms the collection results to CoreTACPrograms.
     *
     * @param results The collecting result containing ProverQuery and CVLError.
     * @return The list of CoreTACPrograms.
     */
    fun transformResultsToTACs(results: CollectingResult<ProverQuery, CVLError>): List<CoreTACProgram> {
        val query = results.force().let {
            it as? ProverQuery.CVLQuery.Single ?: error("expected $it to be a CVLQuery")
        }
        // to ensure assignment won't throw an exception
        EVMTypeDescriptor.resetVTable()
        theSemantics = EVMMoveSemantics
        val scene = SceneFactory.getScene(DummyIContractSource(query.cvl.symbolTable.getAllContracts()), SceneType.PROVER, null)
        val reporter = ReporterContainer(emptyList())
        return IntegrativeChecker.codesToCheck(scene, query, reporter, treeViewReporter = treeViewReporterDummyMock()).getOrThrow().map { it.tac }
    }

    @JvmName("transformResultsToTACsPair")
    fun transformResultsToTACs(results: CollectingResult<Pair<IScene, ProverQuery>, CVLError>): Pair<IScene, List<ICheckableTAC>> {
        val (scene, query) = results.force().mapSecond { q ->
            q as? ProverQuery.CVLQuery.Single ?: error("expected $q to be a CVLQuery")
        }
        EVMTypeDescriptor.resetVTable()
        theSemantics = EVMMoveSemantics
        val reporter = ReporterContainer(emptyList())
        return scene to IntegrativeChecker.codesToCheck(
            scene,
            query,
            reporter,
            treeViewReporter = treeViewReporterDummyMock()
        ).getOrThrow()
    }
}
