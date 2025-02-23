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
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import testing.ttl.TACMockLanguage
import java.math.BigInteger
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract

@OptIn(ExperimentalContracts::class)
fun assertNotNull(x: Any?, msg: String) {
    contract {
        returns() implies (x != null)
    }
    Assertions.assertNotNull(x) {
        msg
    }
}

class LowLevelAllocationTest {
    @Test
    fun testNonLiveReadIsScratch() {
        val (g, res) = this.analyze {
            tagNext("SCRATCH")
            L1024 = freePointer
            mem[L1024] = 12
            tagNext("ALLOC_READ")
            L1024 = freePointer
            L1023 = L1024
            L1023 = "L1023 + 0x20"
            tagNext("ALLOC_WRITE")
            freePointer `=` L(1023)
        }
        assertNotNull(res, "Analysis result")
        val scratchRead = TACMockUtils.commandWithTagOrFail(g, "SCRATCH")
        Assertions.assertTrue(res.scratchReads.containsKey(scratchRead)) {
            "Did not find expected scratch read"
        }
        val readPoint = TACMockUtils.commandWithTagOrFail(g, "ALLOC_READ")
        val writePoint = TACMockUtils.commandWithTagOrFail(g, "ALLOC_WRITE")
        val aloc = res.abstractAllocations[readPoint] ?: Assertions.fail {
            "Failed to find allocation at $readPoint"
        }
        Assertions.assertEquals(writePoint, aloc.nextFPWriteCmd) {
            "Mismatched writes"
        }
    }

    @Test
    fun testScratchInBranch() {
        val (_, res) = this.analyze {
            makeBranchingScratch()
            makeAlloc(resSlot = 1021, tempSlot = 1022, sz = 0x20)
            mem[L1021] = 4
            `return`(L(1020), 0)
        }
        assertNotNull(res, "Analysis failed")
        val aLocs = res.abstractAllocations.values.toSet()
        Assertions.assertEquals(2, aLocs.size)
        Assertions.assertTrue(aLocs.any {
            it.sort.let {
                it is AllocationAnalysis.Alloc.ConstBlock && it.sz == 0x60.toBigInteger()
            }
        }) {
            "Missing size 0x60 alloc"
        }
        Assertions.assertTrue(aLocs.any {
            it.sort.let {
                it is AllocationAnalysis.Alloc.ConstBlock && it.sz == 0x20.toBigInteger()
            }
        }) {
            "Missing post block"
        }
    }

    @Test
    fun testReachingScratchIsFailure() {
        val (_, res) = this.analyze {
            makeBranchingScratch()
            makeAlloc(1021, 1022, 0x20)
            mem[L1024] = 3
            `return`(L(1020), 0)
        }
        Assertions.assertNotNull(res) {
            "Expected analysis to fail without null"
        }
        Assertions.assertTrue(res!!.failureMarkers.isNotEmpty())
    }

    @Test
    fun testWriteSwitchIsScratch() {
        val (graph, res) = this.analyze {
            makeBranchingScratch()
            // this will actually fail in the pointer analysis too, but yolo
            nop // make sure this store has a predecessor, so that we don't fail in ConcreteAllocAnalysis
            mem[L1024] = 3
            `return`(L(1024), 0)
        }
        assertNotNull(res, "Analysis result")
        val readPoint = TACMockUtils.commandWithTagOrFail(graph, "FAIL-READ")
        Assertions.assertTrue(readPoint in res.scratchReads) {
            "$readPoint was not a scratch read?"
        }
    }

    @Test
    fun testDifferentWritesIsFailure() {
        val (_, res) = this.analyze {
            L1024 = `*`
            L1023 = freePointer
            `if`(L(1024)) {
                L1022 = "L1023 + 0x20"
                freePointer `=` L(1022)
            } `else` {
                L1022 = "L1023 + 0x40"
                freePointer `=` L(1022)
            }
            `return`(L(1020), 0)
        }
        Assertions.assertNotNull(res) {
            "Expected analysis to not fail"
        }
        Assertions.assertTrue(res!!.failureMarkers.isNotEmpty())
    }

    @Test
    fun testReachEndIsScratch() {
        val (g, res) = this.analyze {
            L1024 = `*`
            tagNext("HAS-BRANCH")
            L1023 = freePointer
            `if`(L(1024)) {
                exit()
            } `else` {
                mem[L1023] = 4
                makeAlloc(1022, 1021, 0x40, readTag = "ALLOC", writeTag = "WRITE")
                mem[L1022] = 5
                `return`(L(1022), 0x20)
            }
        }
        assertNotNull(res, "Analysis failed")
        val tag = TACMockUtils.commandWithTagOrFail(g, "HAS-BRANCH")
        Assertions.assertTrue(tag in res.scratchReads) {
            "$tag was not scratch"
        }
        val allocPoint = TACMockUtils.commandWithTagOrFail(g, "ALLOC")
        val writePoint = TACMockUtils.commandWithTagOrFail(g, "WRITE")
        Assertions.assertTrue(res.abstractAllocations.get(allocPoint)?.let {
            it.nextFPWriteCmd == writePoint && it.sort.let {
                it is AllocationAnalysis.Alloc.ConstantArrayAlloc
            }
        } == true)
    }

    @Test
    fun testReachEndIsString() {
        // Build a 1 character string (most significant byte must be less than 128)
        val stringConstant = BigInteger.valueOf(1).shiftLeft(254)
        val (g, res) = this.analyze {
            L1024 = `*`
            tagNext("HAS-BRANCH")
            L1023 = freePointer
            `if`(L(1024)) {
                exit()
            } `else` {
                L1021 = "L1023 + 0x40"
                tagNext("WRITE")
                freePointer `=` L(1021)
                L1022 = "L1023 + 0x20"
                mem[L1023] = 1
                mem[L1022] = stringConstant
                `return`(L(1022), 0x20)
            }
        }
        assertNotNull(res, "Analysis failed")
        val tag = TACMockUtils.commandWithTagOrFail(g, "HAS-BRANCH")
        val writePoint = TACMockUtils.commandWithTagOrFail(g, "WRITE")

        Assertions.assertTrue(res.abstractAllocations.get(tag)?.let {
            it.nextFPWriteCmd == writePoint && it.sort.let {
                it is AllocationAnalysis.Alloc.ConstantStringAlloc
            }
        } == true)
    }

    @Test
    fun testPostWriteConstArray() {
        val (g, res) = this.analyze {
            tagNext("ALLOC")
            L1020 = freePointer
            L1021 = "L1020 + 0x40"
            `if`(0, `*`) {
                tagNext("WRITE")
                freePointer `=` L(1021)
                mem[L1020] = 1
            }`else`{
                exit()
            }
        }
        assertNotNull(res, "Analysis failed")
        val tag = TACMockUtils.commandWithTagOrFail(g, "ALLOC")
        val writePoint = TACMockUtils.commandWithTagOrFail(g, "WRITE")
        Assertions.assertTrue(res.abstractAllocations[tag]?.let{
            it.nextFPWriteCmd == writePoint && it.sort.let {
                it is AllocationAnalysis.Alloc.ConstantArrayAlloc && it.constSize == BigInteger.ONE
            }
        } == true)
    }

    @Test
    fun testPostWriteConstArrayHeuristicFail() {
        val (g, res) = this.analyze {
            tagNext("ALLOC")
            L1020 = freePointer
            L1021 = "L1020 + 0x40"
            `if`(0, `*`) {
                tagNext("WRITE")
                freePointer `=` L(1021)
                L1020 = freePointer
                mem[L1020] = 1
            }`else`{
                exit()
            }
        }
        assertNotNull(res, "Analysis failed")
        val tag = TACMockUtils.commandWithTagOrFail(g, "ALLOC")
        val writePoint = TACMockUtils.commandWithTagOrFail(g, "WRITE")
        Assertions.assertTrue(res.abstractAllocations[tag]?.let{
            it.nextFPWriteCmd == writePoint && it.sort.let {
                it is AllocationAnalysis.Alloc.ConstBlock
            }
        } == true)
    }

    private fun TACMockLanguage.StmtBuilderScope.makeAlloc(resSlot: Int, tempSlot: Int, sz: Int, readTag: String? = null, writeTag: String? = null) {
        if(readTag != null) {
            tagNext(readTag)
        }
        L(resSlot) `=` freePointer
        L(tempSlot) `=` "L$resSlot + 0x${sz.toString(16)}"
        if(writeTag != null) {
            tagNext(writeTag)
        }
        freePointer `=` L(tempSlot)
    }

    private fun TACMockLanguage.StmtBuilderScope.makeBranchingScratch(sz: Int = 0x60) {
        L1024 = `*`
        `if`(L(1024)) {
            tagNext("FAIL-READ")
            L1024 = freePointer
        } `else` {
            makeAlloc(1023, 1022, sz)
        }
    }

    private fun analyze(f: TACMockLanguage.StmtBuilderScope.() -> Unit): Pair<TACCommandGraph, AllocationInformation?> {
        val g = TACMockLanguage.make {
            freePointer `=` 0x80
            this.f()
        }
        return g to AllocationAnalysis.runAnalysis(g)
    }
}
