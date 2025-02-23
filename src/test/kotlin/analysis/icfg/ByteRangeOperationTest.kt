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

package analysis.icfg

import evm.EVM_WORD_SIZE
import evm.MASK_SIZE
import net.jqwik.api.Arbitraries
import net.jqwik.api.Arbitrary
import net.jqwik.api.ForAll
import net.jqwik.api.Property
import net.jqwik.api.Provide
import net.jqwik.kotlin.api.combine
import org.junit.jupiter.api.Assertions
import utils.*
import java.math.BigInteger

class ByteRangeOperationTest {
    data class TestPayload(
        val aRange: CallGraphBuilder.ByteRange,
        val bRange: CallGraphBuilder.ByteRange,
        val aConst: BigInteger,
        val bConst: BigInteger
    )

    @Suppress("unused")
    @Provide
    fun nearbyPairs(): Arbitrary<TestPayload> {
        val aStartArb = Arbitraries.bigIntegers().between(EVM_WORD_SIZE + BigInteger.ONE, EVM_WORD_SIZE * BigInteger.TEN)
        val aEndOffsetArb = Arbitraries.bigIntegers().between(BigInteger.ZERO, EVM_WORD_SIZE - BigInteger.ONE)
        val bOffsetStartArb = Arbitraries.bigIntegers().between(EVM_WORD_SIZE.negate(), EVM_WORD_SIZE)
        val bEndOffsetArb = Arbitraries.bigIntegers().between(BigInteger.ZERO, EVM_WORD_SIZE - BigInteger.ONE)
        return combine(aStartArb, aEndOffsetArb, bOffsetStartArb, bEndOffsetArb) { aStart, aEndOffset, bOffsetStart, bEndOffset ->
            val bStart = aStart + bOffsetStart
            CallGraphBuilder.ByteRange(
                start = aStart,
                end = aStart + aEndOffset
            ) to CallGraphBuilder.ByteRange(
                start = bStart,
                end = bStart + bEndOffset
            )
        }.flatMap { (a, b) ->
            val aConst = Arbitraries.bigIntegers().between(BigInteger.ZERO, MASK_SIZE(a.size.intValueExact()))
            val bConst = Arbitraries.bigIntegers().between(BigInteger.ZERO, MASK_SIZE(b.size.intValueExact()))
            combine(aConst, bConst) { c1, c2 ->
                TestPayload(
                    aConst = c1,
                    bConst = c2,
                    aRange = a,
                    bRange = b
                )
            }
        }
    }

    private fun CallGraphBuilder.ByteRange.enumerate(): Sequence<BigInteger> {
        return sequence<BigInteger> {
            var i = this@enumerate.start
            while(i <= this@enumerate.end) {
                yield(i)
                i++
            }
        }
    }

    private fun CallGraphBuilder.ByteRange.asSet() = this.enumerate().toSet()

    private abstract class BigEndianAdapter {
        abstract val widthInBytes: Int
        fun shiftAmount(ind: Int) : Int {
            require(ind < widthInBytes)
            return (widthInBytes - ind - 1) * 8
        }
    }

    private class BigEndianReader(override val widthInBytes: Int, val bitvector: BigInteger) : BigEndianAdapter() {
        constructor(b: CallGraphBuilder.ByteRange, o: BigInteger) : this(b.size.intValueExact(), o)
        operator fun get(ind: Int) : BigInteger {
            return (bitvector shr shiftAmount(ind)) and 0xff.toBigInteger()
        }
    }

    private class BigEndianWriter(override val widthInBytes: Int) : BigEndianAdapter() {
        constructor(b: CallGraphBuilder.ByteRange) : this(b.size.intValueExact())
        var mask: BigInteger = BigInteger.ZERO
        operator fun set(ind: Int, v: BigInteger) {
            require(v and 0xff.toBigInteger() == v)
            mask = mask or (v shl shiftAmount(ind))
        }
    }

    private fun projectRange(o: BigInteger, orig: CallGraphBuilder.ByteRange, newRange: CallGraphBuilder.ByteRange) : BigInteger {
        var sourceIndex = 0
        var outputIndex = 0
        var it = orig.start
        val reader = BigEndianReader(orig, o)
        val writer = BigEndianWriter(newRange)
        while(it <= orig.end && it <= newRange.end) {
            if(it >= newRange.start) {
                writer[outputIndex] = reader[sourceIndex]
                outputIndex++
            }
            it++
            sourceIndex++
        }
        return writer.mask
    }

    @Property(tries = 2500)
    fun testOverwrite(@ForAll("nearbyPairs") nearby: TestPayload) {
        val (a, b, const) = nearby
        when(val o = a.overwriteBy(b)) {
            CallGraphBuilder.ByteRange.OverlapEffect.Contains -> {
                val bLocs = b.asSet()
                Assertions.assertTrue(a.enumerate().all {
                    it in bLocs
                }) {
                    "Claimed $a was strictly contained within $b"
                }
            }
            CallGraphBuilder.ByteRange.OverlapEffect.None -> Assertions.assertFalse(
                a.asSet().containsAny(b.enumerate().asIterable())
            ) {
                "Claimed no overlap for $a, $b"
            }
            is CallGraphBuilder.ByteRange.OverlapEffect.Truncation -> {
                val newRange = o.applyTo(a)
                val bSet = b.asSet()
                val aSet = a.asSet()
                val newRangeIsDistinct = newRange.enumerate().none {
                    it in bSet
                }
                val newRangeIsSubRange = newRange.enumerate().all {
                    it in aSet
                }
                val newSet = newRange.asSet()
                val subRangeIsComplete = a.enumerate().all {
                    it in newSet || it in bSet
                }
                Assertions.assertTrue(subRangeIsComplete && newRangeIsDistinct && newRangeIsSubRange) {
                    "Truncation is broken $a <- $b"
                }
                val newC = o.applyTo(const)
                val expected = projectRange(const, orig = a, newRange = newRange)
                Assertions.assertEquals(expected, newC) {
                    "Mismatch in truncation of indices, have ${newC.toString(16)} vs $expected for $a <- $b and ${const.toString(16)}"
                }
            }
            CallGraphBuilder.ByteRange.OverlapEffect.Hole -> {
                val bLocs = b.asSet()
                var seenBefore = false
                var seenAfter = false
                var seenB = false
                a.enumerate().forEach {
                    if(it !in bLocs) {
                        if(seenB) {
                            seenAfter = true
                        } else {
                            seenBefore = true
                        }
                    } else {
                        seenB = true
                    }
                }
                Assertions.assertTrue(
                    seenB && seenAfter && seenBefore
                ) {
                    "Claimed $b creates a hole within $a"
                }
            }
        }
    }

    @Property(tries = 2500)
    fun testOverlap(@ForAll("nearbyPairs") payload: TestPayload) {
        val (a, b, aConst, bConst) = payload

        fun doOverlap(curr: CallGraphBuilder.ByteRange, other: CallGraphBuilder.ByteRange, currConst: BigInteger) = when(val o = curr.intersect(other)) {
            CallGraphBuilder.ByteRange.OverlapEffect.Contains -> {
                curr to currConst
            }
            CallGraphBuilder.ByteRange.OverlapEffect.None -> {
                val bSet = other.asSet()
                Assertions.assertFalse(bSet.containsAny(curr.enumerate().asIterable())) {
                    "$curr and $other were claimed to not overlap"
                }
                null
            }
            is CallGraphBuilder.ByteRange.OverlapEffect.WithConcreteModel -> {
                o.applyTo(curr) to o.applyTo(currConst)
            }
        }
        fun directedCheck(newRange: CallGraphBuilder.ByteRange, orig: CallGraphBuilder.ByteRange, other: CallGraphBuilder.ByteRange) {
            val otherSet = other.asSet()
            val newSet = newRange.asSet()
            val origSet = orig.asSet()
            val newSetIsOverlapAndSubRange = newSet.all {
                it in otherSet && it in origSet
            }
            val otherElementsNotInOverlap = origSet.all {
                it in newSet || it !in otherSet
            }
            Assertions.assertTrue(newSetIsOverlapAndSubRange && otherElementsNotInOverlap) {
                "Intersection of $a and $b gave conflicting results: $newRange from $orig"
            }
        }

        fun checkConstantAdjust(newRange: CallGraphBuilder.ByteRange, oldRange: CallGraphBuilder.ByteRange, oldC: BigInteger, newC: BigInteger) {
            Assertions.assertEquals(
                projectRange(oldC, oldRange, newRange),
                newC
            ) {
                "Constant projection broken: intersection of $a & $b but $oldRange -> $newRange have ${oldC.toString(16)} -> ${newC.toString(16)}"
            }
        }


        val aSide = doOverlap(a, b, aConst)
        if(aSide != null) {
            val (newARange, newAConst) = aSide
            directedCheck(newARange, a, b)
            checkConstantAdjust(newRange = newARange, oldRange = a, oldC = aConst, newC = newAConst)
        }

        val bSide = doOverlap(b, a, bConst)
        if(bSide != null) {
            val (newBRange, newBConst) = bSide
            directedCheck(newBRange, b, a)
            checkConstantAdjust(newBRange, b, bConst, newBConst)
        }

        Assertions.assertEquals(aSide == null, bSide == null) {
            "Disagreement about disjointedness for $a & $b"
        }
        if(aSide != null && bSide != null) {
            Assertions.assertEquals(aSide.first, bSide.first) {
                "Disagreement about actual overlapping range $a & $b"
            }
        }
    }
}
