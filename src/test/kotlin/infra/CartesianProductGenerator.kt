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

import org.junit.jupiter.params.provider.Arguments
import java.util.stream.Stream

@Suppress("UNUSED_OBJECT")
object CartesianProductGenerator {
    private fun <T> getCartesianProduct(input: List<List<T>>): List<List<T>> {
        if (input.isEmpty()) return listOf(emptyList())

        val result = mutableListOf<List<T>>()

        val head = input[0]
        val tail = input.drop(1)

        val recursiveResult = getCartesianProduct(tail)

        for (h in head) {
            for (r in recursiveResult) {
                val permutation = mutableListOf(h)
                permutation.addAll(r)
                result.add(permutation)
            }
        }

        return result
    }

    private inline fun <reified T> getTestArguments(input: List<List<T>>): Stream<Arguments> {
        return getCartesianProduct(input).map { Arguments.of(*it.toTypedArray()) }.stream()
    }

    @JvmStatic
    fun testQuantifiers(): Stream<Arguments> {
        return getTestArguments(
            listOf(
                listOf("forall", "exists")
            )
        )
    }

    @JvmStatic
    fun testQuantifiersWithTypesRequire(): Stream<Arguments> {
        return getTestArguments(
            listOf(
                listOf("uint8", "int256", "uint256"),
                listOf("forall", "exists"),
                listOf("require", "assert")
            )
        )
    }

    @JvmStatic
    fun testSummary(): Stream<Arguments> {
        return getTestArguments(
            listOf(
                listOf("internal", "external"),
                listOf("ALWAYS(1)", "NONDET")
            )
        )
    }
}
