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

package analysis.abi

import analysis.pta.abi.FieldPointer
import analysis.pta.abi.StridePath
import analysis.pta.abi.StrideStep
import analysis.pta.abi.StridingQualifier
import datastructures.stdcollections.*
import evm.EVM_WORD_SIZE
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import tac.Tag
import vc.data.TACSymbol
import java.math.BigInteger

class StrideJoiningTest {
    private data class TestQualifier(
            override val stridePath: StridePath,
            override val strideBy: BigInteger,
            override val innerOffset: BigInteger
    ) : StridingQualifier {
        fun withPath(stridePath: StridePath): TestQualifier {
            return this.copy(stridePath = stridePath)
        }
    }

    private fun rootPath(r: Int) = StridePath(root = r.toBigInteger(), path = listOf())

    private data class DummyField(override val offset: BigInteger) : FieldPointer {
        constructor(offset: Int) : this(offset.toBigInteger())
    }

    private val dummyVar = TACSymbol.Var(
            namePrefix = "dummy",
            tag = Tag.Bit256
    )

    private fun assertJoinIs(v1: TestQualifier, v2: TestQualifier, expected: TestQualifier) {
        assertJoinCommutative(v1, v2)
        val s = StridingQualifier.joinStridePaths(v1, v2, TestQualifier::withPath) ?: Assertions.fail("Join of $v1 and $v2 returned null")
        Assertions.assertEquals(expected, s) {
            "Join of $v1 and $v2"
        }
    }

    private fun assertJoinIs(v1: TestQualifier, v2: DummyField, expected: TestQualifier) {
        val s = StridingQualifier.joinStridingAndField(left = v1, right = v2) ?: Assertions.fail("Join of $v1 and $v2 returned null")
        Assertions.assertEquals(expected, s) {
            "Join of $v1 and $v2"
        }
    }

    private fun assertJoinIs(v1: TestQualifier, v2: DummyField) {
        assertJoinIs(v1, v2, v1)
    }

    private fun assertJoinCommutative(v1: TestQualifier, v2: TestQualifier) {
        val s1 = StridingQualifier.joinStridePaths(v1, v2, TestQualifier::withPath) ?: Assertions.fail("$v1 and $v2 returned null")
        val s2 = StridingQualifier.joinStridePaths(v2, v1, TestQualifier::withPath) ?: Assertions.fail("$v2 and $v1 returned null")
        Assertions.assertEquals(s1, s2) {
            "Join is not commutative for $v1 and $v2"
        }
    }

    private fun doubleWordStride(root: BigInteger = BigInteger.ZERO) : TestQualifier {
        return TestQualifier(
                stridePath = StridePath(
                    root = root,
                    path = listOf()
                ),
                strideBy = 64.toBigInteger(),
                innerOffset = BigInteger.ZERO
        )
    }

    private fun strideBy(strideBy: Int): TestQualifier {
        return TestQualifier(
                stridePath = StridePath(
                        root = BigInteger.ZERO,
                        path = listOf()
                ),
                strideBy = strideBy.toBigInteger(),
                innerOffset = BigInteger.ZERO
        )
    }

    @Test
    fun testSimpleFieldJoin() {
        assertJoinIs(doubleWordStride(), DummyField(BigInteger.ZERO))
    }

    @Test
    fun testOffsetFieldJoin() {
        assertJoinIs(doubleWordStride().copy(innerOffset = EVM_WORD_SIZE), DummyField(EVM_WORD_SIZE))
    }

    @Test
    fun testMismatchStrides() {
        val expected = TestQualifier(
                strideBy = EVM_WORD_SIZE,
                stridePath = StridePath(
                        root = BigInteger.ZERO,
                        path = listOf(StrideStep.StrideLoop(EVM_WORD_SIZE * BigInteger.TWO))
                ),
                innerOffset = BigInteger.ZERO
        )
        return assertJoinIs(
                strideBy(32),
                strideBy(64),
                expected
        )
    }

    @Test
    fun testRootOffset() {
        val expected = TestQualifier(
                strideBy = EVM_WORD_SIZE,
                stridePath = StridePath(
                        root = BigInteger.ZERO,
                        path = listOf(StrideStep.StrideLoop(256.toBigInteger()), StrideStep.ConstStep(128.toBigInteger()))
                ),
                innerOffset = BigInteger.ZERO
        )
        val stepped = TestQualifier(
                strideBy = 256.toBigInteger(),
                stridePath = StridePath(root = BigInteger.ZERO, path = listOf()),
                innerOffset = 128.toBigInteger()
        )
        val start = TestQualifier(
                stridePath = StridePath(
                        root = 128.toBigInteger(),
                        path = listOf()
                ),
                innerOffset = BigInteger.ZERO,
                strideBy = EVM_WORD_SIZE
        )
        assertJoinIs(stepped, start, expected)
    }

    @Test
    fun testComplicatedNesting() {
        /*
          Example:
          struct A {
             uint pad;
             B[3] parent;
          }
          struct B {
              uint pad1;
              uint pad2;
              C[5] c;
          }
          struct C {
              uint pad1;
              uint[3] c;
          }

          the stride for c is:
          StridePath(
             root = EVM_WORD_SIZE,
             path = StrideLoop(Loop(704), Offset(64), Loop(128), Offset(32))
          )
          the size of B is 32 + 32 + 5 * (32 + 3 * 32) == 704
         */
        val initCStride = TestQualifier(
                stridePath = rootPath(32 * 4),
                innerOffset = BigInteger.ZERO,
                strideBy = EVM_WORD_SIZE
        )
        val cInsideBStride = TestQualifier(
                stridePath = rootPath(3*32),
                strideBy = (32 * 4).toBigInteger(),
                innerOffset = EVM_WORD_SIZE
        )

        val firstLevelJoin = TestQualifier(
                strideBy = EVM_WORD_SIZE,
                innerOffset = BigInteger.ZERO,
                stridePath = StridePath(
                        root = 96,
                        path = listOf(
                                StrideStep.StrideLoop(32 * 4),
                                StrideStep.ConstStep(32)
                        )
                )
        )
        val c5StartInsideB3Loop = TestQualifier(
                strideBy = 704.toBigInteger(),
                innerOffset = 64.toBigInteger(),
                stridePath = rootPath(32)
        )

        val c5StartInFirstB = TestQualifier(
                stridePath = rootPath(96),
                innerOffset = BigInteger.ZERO,
                strideBy = 128.toBigInteger()
        )

        val expectedC5StartInsideB3Loop = TestQualifier(
                strideBy = 128.toBigInteger(),
                innerOffset = BigInteger.ZERO,
                stridePath = StridePath(
                        32,
                        listOf(StrideStep.StrideLoop(704), StrideStep.ConstStep(64))
                )
        )

        val inputUint3StartInsideC5B3Loop = expectedC5StartInsideB3Loop.copy(innerOffset = EVM_WORD_SIZE)

        val expectedUint3StartInsideC5B3Loops = TestQualifier(
                stridePath = StridePath(
                        root = 32,
                        path = listOf(
                                StrideStep.StrideLoop(704),
                                StrideStep.ConstStep(64),
                                StrideStep.StrideLoop(128),
                                StrideStep.ConstStep(32)
                        )
                ),
                innerOffset = BigInteger.ZERO,
                strideBy = EVM_WORD_SIZE
        )

        assertJoinIs(initCStride, cInsideBStride, firstLevelJoin)
        assertJoinIs(c5StartInFirstB, c5StartInsideB3Loop, expectedC5StartInsideB3Loop)
        assertJoinIs(firstLevelJoin, inputUint3StartInsideC5B3Loop, expectedUint3StartInsideC5B3Loops)

    }

    @Test
    fun testExtend() {
        val expected = TestQualifier(
                strideBy = EVM_WORD_SIZE,
                stridePath = StridePath(
                        root = BigInteger.ZERO,
                        path = listOf(StrideStep.StrideLoop(160.toBigInteger()))
                ),
                innerOffset = BigInteger.ZERO
        )
        val initial = TestQualifier(
                stridePath = StridePath(
                        root = BigInteger.ZERO,
                        path = listOf()
                ),
                innerOffset = BigInteger.ZERO,
                strideBy = EVM_WORD_SIZE
        )
        assertJoinIs(initial, expected, expected)
    }
}
