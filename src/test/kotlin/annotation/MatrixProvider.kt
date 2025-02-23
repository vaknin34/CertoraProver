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

package annotation

import org.junit.jupiter.params.provider.Arguments
import java.util.stream.Stream

interface MatrixProvider {
    fun provideMatrix(x: SolidityConfigMatrix): Stream<Arguments> {
        return (if(x.withHeaders) {
            x.headers.map {
                listOf<Any>(it)
            }
        } else {
            listOf(listOf())
        }).flatMap { curr ->
            if(x.withOptimizeFlag) {
                listOf(true, false).map {
                    listOf(it) + curr
                }
            } else {
                listOf(curr)
            }
        }.flatMap {curr ->
            x.solidityVersion.map {
                listOf(it.compilerName()) + curr
            }
        }.map {
            Arguments.of(*it.toTypedArray())
        }.stream()
    }
}
