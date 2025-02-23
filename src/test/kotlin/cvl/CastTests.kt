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

package cvl

import bridge.types.PrimitiveType
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import spec.CastType
import spec.cvlast.CVLType
import java.util.stream.Stream
import kotlin.streams.asStream

@Suppress("unused")
class CastTests : CVLTestHarness() {


    companion object {
        /**
         * Generates a stream of castOp,fromType,toType arguments for tests
         */
        @JvmStatic
        fun castAndTwoTypes(): Stream<Arguments> {
            return sequence {
                CastType.values().map { cast ->
                    representativeCommonTypes.map { fromType ->
                        representativeCommonTypes.map { toType ->
                            yield(Arguments.of(cast.str, fromType, toType))
                        }
                    }
                }
            }.asStream()
        }
    }

    val castTest = { cast: String, type: CVLType, toType: CVLType ->
        generateSingleParameterlessRule(
            """
            $type x;
            $toType y = ${cast}_${toType}(x);
            assert true;
        """
        )
    }

    private fun isIntegerType(t: CVLType): Boolean =
        t is CVLType.PureCVLType && t isSubtypeOf CVLType.PureCVLType.Primitive.Mathint

    // this test is disabled - please reenable to see where this fails
    /*

    @ParameterizedTest
    @MethodSource("castAndTwoTypes")
    fun testCast(cast: String, type: CVLType, toType: CVLType) {
        val ruleTxt = castTest(cast, type, toType)
        // legal toType is an integer type, from type is an integer type
        if (isIntegerType(type) && isIntegerType(toType)) {
            assertTypeChecks(ruleTxt)
        } else {
            assertNotTypeChecks(ruleTxt)
        }
    }
    */

}
