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

import org.junit.jupiter.api.extension.ExtensionContext
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.ArgumentsProvider
import org.junit.jupiter.params.support.AnnotationConsumer
import java.util.stream.Stream

class SolidityConfigMatrixConsumer : ArgumentsProvider, AnnotationConsumer<SolidityConfigMatrix>, MatrixProvider {
    private lateinit var matrix: SolidityConfigMatrix

    override fun provideArguments(context: ExtensionContext?): Stream<out Arguments> {
        return this.provideMatrix(matrix)
    }

    override fun accept(t: SolidityConfigMatrix?) {
        matrix = t ?: error("Got null matrix")
    }

}
