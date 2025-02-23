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
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.EnumSource
import org.junit.jupiter.params.provider.MethodSource
import spec.cvlast.CVLType
import spec.cvlast.typechecker.NotConvertible
import spec.cvlast.typedescriptors.EVMTypeDescriptor
import spec.cvlast.typedescriptors.ISOVMTypeDescriptor
import java.util.stream.Stream
import kotlin.streams.asStream

class MathTests : CVLTestHarness() {

    /**
     * basic math operations and their CVL OP syntax
     */
    enum class MathOp(val cvlOp: String) {
        PLUS("+"),
        MUL("*"),
        MINUS("-"),
        DIV("/"),
    }

    /**
     * basic arithmetic comparisons and their CVL OP syntax
     */
    enum class RelOp(val relOp: String) {
        GT(">"),
        GE(">="),
        LT("<"),
        LE("<="),
    }

    /**
     * returns true if the given primitive type [type] is not an Int or UInt
     */
    private fun nonInteger(type: PrimitiveType): Boolean {
        return type.toDescriptor() !is EVMTypeDescriptor.IntK && type.toDescriptor() !is EVMTypeDescriptor.UIntK
    }

    companion object {
        /**
         * Generates a stream of type,type,mathOp arguments for tests
         */
        @JvmStatic
        fun twoTypesAndOp(): Stream<Arguments> {
            return sequence {
                representativePrimitiveTypes.map { type1 ->
                    representativePrimitiveTypes.map { type2 ->
                        MathOp.values().map { op ->
                            yield(Arguments.of(type1, type2, op))
                        }
                    }
                }
            }.asStream()
        }

        /**
         * Generates a stream of type,type,relOp arguments for tests
         */
        @JvmStatic
        fun twoTypesAndRelOp(): Stream<Arguments> {
            val arithComparibleType = representativePrimitiveTypes.filterNot {
                // the `simpleUintTypes` test checks that the filtered-out types here are not comparable at all
                it == PrimitiveType.byte || it == PrimitiveType.bool || it.toDescriptor() is EVMTypeDescriptor.BytesK
            } + PrimitiveType.address

            return sequence {
                arithComparibleType.map { type1 ->
                    arithComparibleType.map { type2 ->
                        RelOp.values().map { op ->
                            yield(Arguments.of(type1, type2, op))
                        }
                    }
                }
            }.asStream()
        }
    }

    @Test
    fun simpleRule() {
        assertTypeChecks(
            generateSingleParameterlessRule(
                "assert 3 > 1;"
            )
        )
    }

    val simpleUintRule = { type: String ->
        generateSingleParameterlessRule(
            """
                $type x;
                assert x > 0;
        """
        )
    }

    @ParameterizedTest
    @EnumSource(PrimitiveType::class)
    fun simpleUintTypes(type: PrimitiveType) {
        val ruleTxt = simpleUintRule(type.name)
        if (type == PrimitiveType.byte) {
            assertSyntaxError(
                ruleTxt,
                "byte is not a valid CVL type"
            )
        } else if (type == PrimitiveType.nonreentrant_lock) {
            assertSyntaxError(
                ruleTxt,
                "nonreentrant_lock is not a valid CVL type"
            )
        } else {
            when (type.toDescriptor()) {
                is EVMTypeDescriptor.UIntK,
                is EVMTypeDescriptor.IntK,
                is EVMTypeDescriptor.address -> assertTypeChecks(ruleTxt)
                else -> assertNotTypeChecksWithError(
                    ruleTxt,
                    "x isn't a subtype of mathint so isn't comparable"  // this is a bad message todo better english
                )
            }
        }
    }

    val arithComparisonRule = { t1: String, t2: String, relOp: String ->
        generateSingleParameterlessRule(
            """
                $t1 x;
                $t2 y;
                assert x $relOp y;
            """.trimIndent()
        )
    }

    @ParameterizedTest
    @MethodSource("twoTypesAndRelOp")
    fun relOp(t1: PrimitiveType, t2: PrimitiveType, relOp: RelOp) {
        val ruleTxt = arithComparisonRule(t1.name, t2.name, relOp.relOp)
        if (t1.toDescriptor() != t2.toDescriptor()) { // using the descriptors for comparison so that we'll consider uint256 and uint as the same type
            if (t1 == PrimitiveType.address) {
                assertNotTypeChecksWithError(
                    ruleTxt,
                    "x of type 'address' can only be compared to another address, not ${t2.toDescriptor()}"
                )
            } else if (t2 == PrimitiveType.address) {
                assertNotTypeChecksWithError(
                    ruleTxt,
                    "y of type 'address' can only be compared to another address, not ${t1.toDescriptor()}"
                )
            } else {
                assertTypeChecks(ruleTxt)
            }
        } else if ((t1.toDescriptor() as ISOVMTypeDescriptor).isomorphicType.force() !is CVLType.PureCVLType.Primitive.BytesK){
            assertTypeChecks(ruleTxt)
        } else {
            assertNotTypeChecksWithError(
                ruleTxt,
                "x isn't a subtype of mathint so isn't comparable"
            )
        }
    }

    val mathOpRule = { type1: String, type2: String, op: String ->
        generateSingleParameterlessRule(
        """
            $type1 x;
            $type2 y;
            assert x $op y > 0;
        """
        )
    }

    @ParameterizedTest
    @MethodSource("twoTypesAndOp")
    fun mathOp(type1: PrimitiveType, type2: PrimitiveType, op: MathOp) {
        val ruleTxt = mathOpRule(type1.name, type2.name, op.cvlOp)
        val descriptor1 = type1.toDescriptor()
        val descriptor2 = type2.toDescriptor()
        if (type1 == PrimitiveType.byte || type2 == PrimitiveType.byte) {
            assertSyntaxError(
                ruleTxt,
                "byte is not a valid CVL type"
            ) // this is a bad message todo
        } else if (type1 == PrimitiveType.nonreentrant_lock || type2 == PrimitiveType.nonreentrant_lock) {
            assertSyntaxError(
                ruleTxt,
                "nonreentrant_lock is not a valid CVL type"
            )
        } else if (!nonInteger(type2) && descriptor1 is EVMTypeDescriptor.BytesK) {
            assert(getSingleError<NotConvertible>(ruleTxt).message.contains("x")) { "message is not about x" }
        } else if (!nonInteger(type1) && descriptor2 is EVMTypeDescriptor.BytesK) {
            assert(getSingleError<NotConvertible>(ruleTxt).message.contains("y")) { "message is not about y" }
        } else if (nonInteger(type1) || nonInteger(type2)) {
            assertNotTypeChecks(ruleTxt)
        } else {
            assertTypeChecks(ruleTxt)
        }
    }


}
