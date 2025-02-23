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

package analysis

import analysis.alloc.AllocationAnalysis
import analysis.alloc.AllocationInformation
import annotation.ScopedVersions
import annotation.SolidityVersion
import annotation.SolidityVersions
import annotation.WithOptimizedFlag
import loaders.SingleMethodTest
import loaders.SolidityContractTest
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.params.ParameterizedTest
import testing.wrapInTrivialContract
import java.math.BigInteger

private val packedByteArray = """
    bytes memory z = abi.encodePacked(uint(3), uint128(5), uint8(16));
    return z.length;
""".trimIndent().wrapInTrivialContract("uint")

private val fakeScratch = """
    bytes32 hash = bytes32(uint(2));
	uint8 v = uint8(3);
	bytes32 r = bytes32(uint(4));
	bytes32 s = bytes32(uint(5));
    address foo = ecrecover(hash, v, r, s);
    return foo;
""".trimIndent().wrapInTrivialContract("address")


inline fun <reified T> assertIs(x: Any, kls: Class<T>) {
    assertEquals(kls, x.javaClass) {
        "Wrong type"
    }
    check(x is T)
}

private const val msg = "Comp::_writeCheckpoint: block number exceeds 32 bits"

private val constantString = """
    string memory msg = "$msg";
""".trimIndent().wrapInTrivialContract()

@SolidityVersions([SolidityVersion.V5_16, SolidityVersion.ANY_5, SolidityVersion.V6_8, SolidityVersion.V6_10, SolidityVersion.V7_0])
class AllocationTest : SingleMethodTest, SolidityContractTest {
    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testPackedByteArrayAlloc(solc: String, optimize: Boolean) {
        runAllocAnalysis(packedByteArray, solc, optimize) { x ->
            val allocs = x.abstractAllocations.values.toSet()
            assertEquals(1, allocs.size) {
                "Got all these allocs! $allocs"
            }
            val alloc = allocs.first()
            assertTrue(alloc.sort is AllocationAnalysis.Alloc.PackedByteArray)
        }
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testFakeScratch(solc: String, optimize: Boolean) {
        runAllocAnalysis(fakeScratch, solc, optimize) {
            assertEquals(0, it.abstractAllocations.size) {
                "Found an unexpected allocation"
            }
            assertTrue(it.scratchReads.isNotEmpty()) {
                "Found multiple scratch reads"
            }
            assertTrue(it.scratchReads.any { it.value.map { it == 32.toBigInteger() }.orElse(false) } ) {
                "Did not find offset 32 scratch read"
            }
            assertTrue(it.scratchReads.any { it.value.map { it == BigInteger.ZERO }.orElse(false) } ) {
                "Did not find offset 0 scratch read"
            }
        }
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testInterleavedAlloc(solc: String, optimize: Boolean) {
        this.loadTestContractGraph("analysis/InterleavedAlloc.sol", solc, optimize).let {g ->
            runAllocAnalysis(g) {
                assertTrue(it.scratchReads.isNotEmpty()) {
                    "Expected to find some scratch reads"
                }
                assertTrue(it.abstractAllocations.isNotEmpty()) {
                    "Expected to find some allocation"
                }
                assertEquals(2, it.abstractAllocations.size) {
                    "Expected only two abstract allocs ${it.abstractAllocations}"
                }
                it.abstractAllocations.forEach { _, alloc ->
                    assertTrue(alloc.sort is AllocationAnalysis.Alloc.ConstBlock) {
                        "Found a very unexpected alloc type ${alloc.sort}"
                    }
                    assertEquals(64.toBigInteger(), (alloc.sort as AllocationAnalysis.Alloc.ConstBlock).sz) {
                        "Expected to find a two field allocation only"
                    }
                }
            }
        }
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testStructAlloc(solc: String, optimize: Boolean) {
        val g = this.loadTestContractGraph("analysis/BasicStructAlloc.sol", solc, optimize)
        runAllocAnalysis(g) {
            val locs = it.abstractAllocations.values.toSet()
            assertEquals(1, locs.size) {
                "Expected exactly one abstract loc, but instead found $locs"
            }
            val sort = locs.first().sort
            assertTrue(sort is AllocationAnalysis.Alloc.ConstBlock) {
                "Sort is not a constant block"
            }
            assertEquals(0x40.toBigInteger(), (sort as AllocationAnalysis.Alloc.ConstBlock).sz) {
                "Unexpected struct size"
            }
        }
    }

    @ParameterizedTest
    @SolidityVersions(versions = [SolidityVersion.ANY_5, SolidityVersion.V6_10, SolidityVersion.V6_8, SolidityVersion.V7_0])
    @WithOptimizedFlag
    fun testStringAlloc(solc: String, optimize: Boolean) {
        this.runAllocAnalysis(constantString, solc, optimize) {
            val locs = it.abstractAllocations.values.toSet()
            assertEquals(1, locs.size) {
                "Found more than one abstract allocation $locs"
            }
            val loc = locs.first().sort
            assertIs(loc, AllocationAnalysis.Alloc.ConstantStringAlloc::class.java)
            assertEquals(msg.length.toBigInteger(), (loc as AllocationAnalysis.Alloc.ConstantStringAlloc).constLen) {
                "Bad length"
            }
        }
    }

    private fun runAllocAnalysis(src: String, solc: String, optimize: Boolean, f: (AllocationInformation) -> Unit) {
        val graph = loadTestGraph(src, solc, optimize)
        return this.runAllocAnalysis(graph, f)
    }

    private fun runAllocAnalysis(graph: TACCommandGraph, f: (AllocationInformation) -> Unit) {
        val x = AllocationAnalysis.runAnalysis(graph)
        assertNotNull(x) {
            "The allocation analysis failed"
        }
        check(x != null)
        f(x)
    }


    @ParameterizedTest
    @SolidityVersions(versions = [SolidityVersion.V5_16, SolidityVersion.ANY_5, SolidityVersion.V6_8, SolidityVersion.V6_10, SolidityVersion.V7_0])
    @WithOptimizedFlag
    fun recognizeStringAlloc(solc: String, optimize: Boolean) {
        runAllocAnalysis(loadTestContractGraph("analysis/ShortStringRequire.sol", solc, optimize)) {
            Assertions.assertEquals(1, it.abstractAllocations.size)
            val x = it.abstractAllocations.values.first()
            Assertions.assertTrue(x.sort is AllocationAnalysis.Alloc.ConstantStringAlloc)
        }
    }
}
