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

package verifier

import kotlin.io.path.Path
import config.Config
import datastructures.stdcollections.*
import smt.UseLIAEnum
import smt.UseLIAEnumConverter
import solver.SolverChoice
import utils.*

class TACVerifierConfig {
    private val resourceLabel = "autoconfigFile:"
    private val adaptiveSettings: Map<String, TACVerifierSettings> by lazy { loadAdaptiveSettings() }

    @Suppress("ForbiddenMethodCall")
    private fun getAutoconfigPathFromCLI(): String? {
        val resourcesProvided = Config.ResourceFiles.getOrNull() ?: return null
        if (resourcesProvided.any { it.startsWith(resourceLabel) }) {
            val path = resourcesProvided.single { it.startsWith(resourceLabel) }.substring(resourceLabel.length).trim()

            //this adds path to .certora_sources as a prefix to work correctly on cloud
            return ArtifactFileUtils.wrapPathWith(path, Config.getSourcesSubdirInInternal())
        }
        return null
    }

    data class TACVerifierSettings(
        val configSolverChoice: SolverChoice? = null,
        val useNIA: Boolean? = null,
        val useLIA: UseLIAEnum? = null,
        val liaSolvers: SolverChoice? = null,
        val niaSolvers: SolverChoice? = null,
        val resplit: Boolean? = null,
        val knownToBeUnsat: Boolean? = null,
    ) {
        companion object {
            private fun parseSolverChoice(data: String) =
                SolverChoice(cli.SolverProgramListConverter.convert(data).toList())

            //TODO: CERT-2646 make the parser more robust
            fun parse(data: List<List<String>>): TACVerifierSettings {
                var configSolverChoice: SolverChoice? = null
                var useNIA: Boolean? = null
                var useLIA: UseLIAEnum? = null
                var liaSolvers: SolverChoice? = null
                var niaSolvers: SolverChoice? = null
                var resplit: Boolean? = null
                data.forEach { setting ->
                    when (setting[1]) {
                        "configSolverChoice" -> configSolverChoice = parseSolverChoice(setting[2])
                        "useNIA" -> useNIA = setting[2].toBoolean()
                        "useLIA" -> useLIA = UseLIAEnumConverter.convert(setting[2])
                        "liaSolvers" -> liaSolvers = parseSolverChoice(setting[2])
                        "niaSolvers" -> niaSolvers = parseSolverChoice(setting[2])
                        "resplit" -> resplit = setting[2].toBoolean()
                        else -> throw IllegalArgumentException(setting[1])
                    }
                }
                return TACVerifierSettings(
                    configSolverChoice,
                    useNIA, useLIA, liaSolvers, niaSolvers, resplit
                )
            }
        }
    }

    @Suppress("ForbiddenMethodCall")
    private fun loadAdaptiveSettings(): Map<String, TACVerifierSettings> {
        val adaptiveSettingsFilePath =
            Path(getAutoconfigPathFromCLI() ?: return emptyMap()) //autoconfig file is not provided)

        require(adaptiveSettingsFilePath.toFile().exists())
        { "Autoconfig file not found at ${adaptiveSettingsFilePath.toAbsolutePath()}" }
        return adaptiveSettingsFilePath.toFile().readLines()
            .map { it.split("\t") }
            .onEach { check(it.size == 3) } //just checking that the input file is properly formatted. See the comment below
            .groupBy { it[0] }//groups entries related to the same split
            .map { it.key to TACVerifierSettings.parse(it.value) }
            .toMap()

        //structure of the autoconfig file. The actual file doesn't contain header, fields are tab-separated.
        //vcName                        setting     newValue
        //openLongReallyOpensLong_		resplit     TRUE
        //openLongReallyOpensLong_0     useLIA      FALSE
    }

    fun shouldResplit(vcName: String) = getAdaptiveSettingsForVc(vcName)?.resplit ?: false

    fun getAdaptiveSettingsForVc(vcName: String): TACVerifierSettings? = adaptiveSettings[vcName]

}
