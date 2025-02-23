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

package report

import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.json.Json
import java.io.IOException
import java.io.Serializable

// TODO: Rename this simply to "Features"
object CoinbaseFeatures {
    /**
     * The rules in [depFeatures] are checked first according to their order in [depFeatures].
     * NOTE: All of the rules in [depFeatures] are assumed to be unary, namely that they have one method type parameter.
     * Then, the final result of the rule [featureName] will be determined based on the results of [depFeatures],
     * using [FeatureWithExpectedResult.expectedResult] as oracles.
     * [dualFeature] be be non-null only for binary rules, i.e., rules with two method type parameters.
     * [yesResult] denotes which solver result maps to "YES" for the feature [featureName].
     * Rules are assumed to be either unary or binary.
     */
    @kotlinx.serialization.Serializable
    data class FeatureDeclaration(
        val featureName: String,
        val dualFeature: String?,
        val yesResult: UnderlyingSolverResult,
        val depFeatures: List<FeatureWithExpectedResult>
    ) : Serializable

    @kotlinx.serialization.Serializable
    data class FeatureWithExpectedResult(val id: String, val expectedResult: ExpectedFeatureResult) : Serializable

    enum class UnderlyingSolverResult {
        SAT, UNSAT
    }

    enum class ExpectedFeatureResult {
        YES, NO
    }

    private fun String.deserializeFeatures(): List<FeatureDeclaration> =
        Json.decodeFromString(ListSerializer(FeatureDeclaration.serializer()), this)

    private const val jsonResource = "featuresConfig.json"

    fun deserializeFeatures(): List<FeatureDeclaration> = ClassLoader.getSystemResourceAsStream(jsonResource)?.use {
        it.bufferedReader().use { reader -> reader.readText() }.deserializeFeatures()
    } ?: throw IOException("Could not find $jsonResource")
}