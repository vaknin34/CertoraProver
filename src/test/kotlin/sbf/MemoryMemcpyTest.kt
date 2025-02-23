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

package sbf

import com.certora.collect.*
import sbf.cfg.*
import sbf.disassembler.*
import sbf.domains.*
import sbf.support.UnknownStackContentError
import log.*
import org.junit.jupiter.api.Test
import java.io.ByteArrayOutputStream
import java.io.PrintStream
import org.junit.jupiter.api.*

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class MemoryMemcpyTest {
    private var outContent = ByteArrayOutputStream()
    private var errContent = ByteArrayOutputStream()

    private val originalOut = System.out
    private val originalErr = System.err

    // system properties have to be set before we load the logger
    @BeforeAll
    fun setupAll() {
        System.setProperty(LoggerTypes.SBF.toLevelProp(), "info")
    }

    // we must reset our stream so that we could match on what we have in the current test
    @BeforeEach
    fun setup() {
        outContent = ByteArrayOutputStream()
        errContent = ByteArrayOutputStream()
        System.setOut(PrintStream(outContent, true)) // for 'always' logs
        System.setErr(PrintStream(errContent, true)) // loggers go to stderr
    }

    private fun debug() {
        originalOut.println(outContent.toString())
        originalErr.println(errContent.toString())
    }

    // close and reset
    @AfterEach
    fun teardown() {
        debug()
        System.setOut(originalOut)
        System.setErr(originalErr)
        outContent.close()
        errContent.close()
    }


    // Return node pointed by *([baseR] + [offset])
    private fun getNode(g: PTAGraph,
                        base: Value.Reg, offset: Short, width: Short): PTANode? {
        val lhs = Value.Reg(SbfRegister.R7)
        check(base != lhs)
        val inst = SbfInstruction.Mem(Deref(width, base, offset, null), lhs, true, null)
        val locInst = LocatedSbfInstruction(Label.fresh(), 0, inst)
        g.doLoad(locInst, lhs, base, offset, width, SbfType.Top, newGlobalVariableMap())
        val sc = g.getRegCell(lhs)
        return sc?.node
    }

    // Check that *([baseR] + [offset]) points to [node]
    private fun checkPointsToNode(g: PTAGraph,
                                  base: Value.Reg, offset: Short, width: Short,
                                  node: PTANode) {
        Assertions.assertEquals(true, getNode(g, base, offset, width)?.id == node.id)
    }

    @Test
    fun test01() {
        sbfLogger.info { "====== TEST 1: memcpy from stack to uninitialized stack  (known length) =======" }

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        // Create abstract state
        val absVal = MemoryDomain(PTANodeAllocator(), true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
        stackC.node.mkLink(4040, 8, n1.createCell(0))
        stackC.node.mkLink(4048, 8, n2.createCell(0))
        stackC.node.mkLink(4056, 8, n3.createCell(0))
        g.setRegCell(r2, stackC.node.createSymCell(PTASymOffset(4040)))
        g.setRegCell(r1, stackC.node.createSymCell(PTASymOffset(3040)))

        val scalars = ScalarDomain()
        scalars.setRegister(r3, ScalarValue.from(24UL))
        // memcpy(r1, r2, 24)
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.info {"After memcpy(r1,r2,24) -> $g"}

        checkPointsToNode(g, r1, 0, 8, n1)
        checkPointsToNode(g, r1, 8, 8, n2)
        checkPointsToNode(g, r1, 16, 8, n3)
    }

    @Test
    fun test02() {
        sbfLogger.info { "====== TEST 2: memcpy from (exact) non-stack to uninitialized stack (known length) =======" }

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        // Create abstract state
        val absVal = MemoryDomain(PTANodeAllocator(), true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val srcNode = g.mkNode()
        srcNode.setWrite()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
        stackC.node.mkLink(4040, 8, srcNode.createCell(0))
	    srcNode.mkLink(0, 8, n1.createCell(0))
        srcNode.mkLink(8, 8, n2.createCell(0))
        srcNode.mkLink(16, 8, n3.createCell(0))

        g.setRegCell(r2, srcNode.createSymCell(PTASymOffset(0)))
        g.setRegCell(r1, stackC.node.createSymCell(PTASymOffset(3040)))

        val scalars = ScalarDomain()
        scalars.setRegister(r3, ScalarValue.from(24UL))
        // memcpy(r1, r2, 24)
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.info {"After memcpy(r1,r2,24) -> $g"}

        checkPointsToNode(g, r1, 0, 8, n1)
        checkPointsToNode(g, r1, 8, 8, n2)
        checkPointsToNode(g, r1, 16, 8, n3)
    }

    @Test
    fun test03() {
        sbfLogger.info { "====== TEST 3: memcpy from (exact) non-stack to (exact) uninitialized non-stack (known length) =======" }

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        // Create abstract state
        val absVal = MemoryDomain(PTANodeAllocator(),true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val srcNode = g.mkNode()
        srcNode.setWrite()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
        val dstN = g.mkNode()
        stackC.node.mkLink(4040, 8, srcNode.createCell(0))
	    srcNode.mkLink(0, 8, n1.createCell(0))
        srcNode.mkLink(8, 8, n2.createCell(0))
        srcNode.mkLink(16, 8, n3.createCell(0))

        g.setRegCell(r2, srcNode.createSymCell(PTASymOffset(0)))
        g.setRegCell(r1, dstN.createSymCell(PTASymOffset(0)))

        val scalars = ScalarDomain()
        scalars.setRegister(r3, ScalarValue.from(24UL))
        // memcpy(r1, r2, 24)
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.info {"After memcpy(r1,r2,24) -> $g"}

        Assertions.assertEquals(true, !dstN.isUnaccessed())
        checkPointsToNode(g, r1, 0, 8, n1)
        checkPointsToNode(g, r1, 8, 8, n2)
        checkPointsToNode(g, r1, 16, 8, n3)
    }


    @Test
    fun test04() {
        sbfLogger.info { "====== TEST 4: memcpy from stack to initialized stack (known length) =======" }

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        // Create abstract state
        val absVal = MemoryDomain(PTANodeAllocator(),true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
        val n4 = g.mkNode()
        n4.setWrite()
        val n5 = g.mkNode()
        n5.setWrite()
        val n6 = g.mkNode()
        n6.setWrite()

        stackC.node.mkLink(3040, 8, n4.createCell(0))
        stackC.node.mkLink(3048, 8, n5.createCell(0))
        stackC.node.mkLink(3056, 8, n6.createCell(0))

        stackC.node.mkLink(4040, 8, n1.createCell(0))
        stackC.node.mkLink(4048, 8, n2.createCell(0))
        stackC.node.mkLink(4056, 8, n3.createCell(0))
        g.setRegCell(r2, stackC.node.createSymCell(PTASymOffset(4040)))
        g.setRegCell(r1, stackC.node.createSymCell(PTASymOffset(3040)))

        val scalars = ScalarDomain()
        scalars.setRegister(r3, ScalarValue.from(24UL))
        // memcpy(r1, r2, 24)

        sbfLogger.info {"Before memcpy(r1,r2,24) -> $g"}
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.info {"After memcpy(r1,r2,24) -> $g"}

        checkPointsToNode(g, r1, 0, 8, n1)
        checkPointsToNode(g, r1, 8, 8, n2)
        checkPointsToNode(g, r1, 16, 8, n3)
    }

    @Test
    fun test05() {
        sbfLogger.info { "====== TEST 5: memcpy from (exact) non-stack to initialized stack (known length) =======" }

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        // Create abstract state
        val absVal = MemoryDomain(PTANodeAllocator(), true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val srcNode = g.mkNode()
        srcNode.setWrite()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
	    val n4 = g.mkNode()
        n4.setWrite()
        val n5 = g.mkNode()
        n5.setWrite()
        val n6 = g.mkNode()
        n6.setWrite()

        stackC.node.mkLink(3040, 8, n4.createCell(0))
        stackC.node.mkLink(3048, 8, n5.createCell(0))
        stackC.node.mkLink(3056, 8, n6.createCell(0))

        stackC.node.mkLink(4040, 8, srcNode.createCell(0))
	    srcNode.mkLink(0, 8, n1.createCell(0))
        srcNode.mkLink(8, 8, n2.createCell(0))
        srcNode.mkLink(16, 8, n3.createCell(0))

        g.setRegCell(r2, srcNode.createSymCell(PTASymOffset(0)))
        g.setRegCell(r1, stackC.node.createSymCell(PTASymOffset(3040)))

        val scalars = ScalarDomain()
        scalars.setRegister(r3, ScalarValue.from(24UL))
        // memcpy(r1, r2, 24)
        sbfLogger.info {"Before memcpy(r1,r2,24) -> $g"}
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.info {"After memcpy(r1,r2,24) -> $g"}

        checkPointsToNode(g, r1, 0, 8, n1)
        checkPointsToNode(g, r1, 8, 8, n2)
        checkPointsToNode(g, r1, 16, 8, n3)
    }


    @Test
    fun test06() {
        sbfLogger.info { "====== TEST 6: memcpy from (exact) non-stack to (exact) initialized non-stack (known length) =======" }

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        // Create abstract state
        val absVal = MemoryDomain(PTANodeAllocator(), true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val srcNode = g.mkNode()
        srcNode.setWrite()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
        val dstN = g.mkNode()

        val n4 = g.mkNode()
        n4.setWrite()
        val n5 = g.mkNode()
        n5.setWrite()
        val n6 = g.mkNode()
        n6.setWrite()

        dstN.mkLink(0, 8, n4.createCell(0))
        dstN.mkLink(8, 8, n5.createCell(0))
        dstN.mkLink(16, 8, n6.createCell(0))

        stackC.node.mkLink(4040, 8, srcNode.createCell(0))
	    srcNode.mkLink(0, 8, n1.createCell(0))
        srcNode.mkLink(8, 8, n2.createCell(0))
        srcNode.mkLink(16, 8, n3.createCell(0))

        g.setRegCell(r2, srcNode.createSymCell(PTASymOffset(0)))
        g.setRegCell(r1, dstN.createSymCell(PTASymOffset(0)))

        val scalars = ScalarDomain()
        scalars.setRegister(r3, ScalarValue.from(24UL))
        // memcpy(r1, r2, 24)
        sbfLogger.info {"Before memcpy(r1,r2,24) -> $g"}
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.info {"After memcpy(r1,r2,24) -> $g"}

        Assertions.assertEquals(true, !n4.isUnaccessed())
        checkPointsToNode(g, r1, 0, 8, n1)
        checkPointsToNode(g, r1, 8, 8, n2)
        checkPointsToNode(g, r1, 16, 8, n3)
    }

    @Test
    fun test07() {
        sbfLogger.info { "====== TEST 7: memcpy from (exact) non-stack to (exact) initialized non-stack (unknown length) =======" }

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)

        // Create abstract state
        val absVal = MemoryDomain(PTANodeAllocator(), true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val srcNode = g.mkNode()
        srcNode.setWrite()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
        val dstN = g.mkNode()

        val n4 = g.mkNode()
        n4.setWrite()
        val n5 = g.mkNode()
        n5.setWrite()
        val n6 = g.mkNode()
        n6.setWrite()

        dstN.mkLink(0,  8, n4.createCell(0))
        dstN.mkLink(8, 8, n5.createCell(0))
        dstN.mkLink(16, 8, n6.createCell(0))

        stackC.node.mkLink(4040, 8, srcNode.createCell(0))
	    srcNode.mkLink(0, 8, n1.createCell(0))
        srcNode.mkLink(8, 8, n2.createCell(0))
        srcNode.mkLink(16, 8, n3.createCell(0))

        g.setRegCell(r2, srcNode.createSymCell(PTASymOffset(0)))
        g.setRegCell(r1, dstN.createSymCell(PTASymOffset(0)))

        val scalars = ScalarDomain()
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        scalars.setRegister(r3, ScalarValue.anyNum())
        // memcpy(r1, r2, r3)
        sbfLogger.info {"Before memcpy(r1,r2,r3) with r3=top -> $g"}
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.info {"After memcpy(r1,r2,r3) with r3=top -> $g"}

        // It should unify the nodes pointed by src with those pointed by dst.
        Assertions.assertEquals(true, g.getRegCell(r1) == g.getRegCell(r2))
    }

    @Test
    fun test08() {
        sbfLogger.info { "====== TEST 8: memcpy from (exact) non-stack to initialized stack (unknown length) =======" }

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)

        // Create abstract state
        val absVal = MemoryDomain(PTANodeAllocator(),true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val srcNode = g.mkNode()
        srcNode.setWrite()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
	    val n4 = g.mkNode()
        n4.setWrite()
        val n5 = g.mkNode()
        n5.setWrite()
        val n6 = g.mkNode()
        n6.setWrite()

        stackC.node.mkLink(3040, 8, n4.createCell(0))
        stackC.node.mkLink(3048, 8, n5.createCell(0))
        stackC.node.mkLink(3056, 8, n6.createCell(0))

        stackC.node.mkLink(4040, 8, srcNode.createCell(0))
	    srcNode.mkLink(0, 8, n1.createCell(0))
        srcNode.mkLink(8, 8, n2.createCell(0))
        srcNode.mkLink(16, 8, n3.createCell(0))

        g.setRegCell(r2, srcNode.createSymCell(PTASymOffset(0)))
        g.setRegCell(r1, stackC.node.createSymCell(PTASymOffset(3040)))

        val scalars = ScalarDomain()
        var exception = false
        try {
            // memcpy(r1, r2, r3)
            sbfLogger.warn {"Before memcpy(r1,r2,r3) with r3=top -> $g"}
            g.doMemcpy(scalars, newGlobalVariableMap())
            sbfLogger.info {"After memcpy(r1,r2,r3) with r3=top -> $g"}
        }
        catch (e: PointerDomainError) {
            sbfLogger.warn {"Test failed as expected because $e"}
            exception = true
        }
        Assertions.assertEquals(true, exception)
    }

    @Test
    fun test09() {
        sbfLogger.info { "====== TEST 9: memcpy from summarized to stack =======" }
        /**
         * ```
         * dst = [(3030,8) -> (n4,0), (3040,8) -> (n4,0),  (3048,8) -> (n5,0), (3056,8) -> (n6,0)]
         * src = [(0,8) -> (n1,0), (8,8) -> (n2,0), (16,8) -> (n3,0)] --> SummarizedNode -> (n7,0)
         *
         * after memcpy 24 bytes from "any" to 3040:
         * dst = [(3030,8) -> (n4,0), (3040,8) -> (n7,0), (3048,8) -> (n7,0), (3056,8) -> (n7,0)]
         * ```
         */

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        // Create abstract state
        val absVal = MemoryDomain(PTANodeAllocator(),true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val srcNode = g.mkSummarizedNode()
        srcNode.setWrite()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
	    val n4 = g.mkNode()
        n4.setWrite()
        val n5 = g.mkNode()
        n5.setWrite()
        val n6 = g.mkNode()
        n6.setWrite()

        stackC.node.mkLink(3030, 8, n4.createCell(0))
        stackC.node.mkLink(3040, 8, n4.createCell(0))
        stackC.node.mkLink(3048, 8, n5.createCell(0))
        stackC.node.mkLink(3056, 8, n6.createCell(0))

        stackC.node.mkLink(4040, 8, srcNode.createCell(0))
	    srcNode.mkLink(0, 8, n1.createCell(0))
        srcNode.mkLink(8, 8, n2.createCell(0))
        srcNode.mkLink(16, 8, n3.createCell(0))

        g.setRegCell(r2, srcNode.createSymCell(PTASymOffset(0)))
        g.setRegCell(r1, stackC.node.createSymCell(PTASymOffset(3040)))

        val scalars = ScalarDomain()
        // memcpy(r1, r2, 24)
        scalars.setRegister(r3, ScalarValue.from(24UL))
        sbfLogger.warn {"Before memcpy(r1,r2,24) -> $g"}
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.warn {"After memcpy(r1,r2,24) -> $g"}


        val c1 = stackC.node.getSucc(PTAField(3030, 8))
        val c2 = stackC.node.getSucc(PTAField(3040, 8))
        val c3 = stackC.node.getSucc(PTAField(3048, 8))
        val c4 = stackC.node.getSucc(PTAField(3056, 8))

        Assertions.assertEquals(true,  c1 != c2 && c2 == c3 && c3 == c4 && c4 != null)
    }

    @Test
    fun test10() {
        sbfLogger.info { "====== TEST 10: memcpy from stack to summarized   =======" }
        /**
         * ```
         * dst = [(0,8) -> (n1,0), (8,8) -> (n2,0), (16,8) -> (n3,0)] --> SummarizedNode -> (n7,0)
         * src = [(3030,8) -> (n4,0), (3040,8) -> (n4,0),  (3048,8) -> (n5,0), (3056,8) -> (n6,0)]
         *
         * after memcpy 24 bytes from src 3040 to dst at "any":
         * dst = [(3030,8) -> (n7,0), (3040,8) -> (n7,0), (3048,8) -> (n7,0), (3056,8) -> (n7,0)]
         * ```
         */

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        // Create abstract state
        val absVal = MemoryDomain(PTANodeAllocator(),true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val dstNode = g.mkSummarizedNode()
        dstNode.setWrite()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
        val n4 = g.mkNode()
        n4.setWrite()
        val n5 = g.mkNode()
        n5.setWrite()
        val n6 = g.mkNode()
        n6.setWrite()

        stackC.node.mkLink(3030, 8, n4.createCell(0))
        stackC.node.mkLink(3040, 8, n4.createCell(0))
        stackC.node.mkLink(3048, 8, n5.createCell(0))
        stackC.node.mkLink(3056, 8, n6.createCell(0))

        stackC.node.mkLink(4040, 8, dstNode.createCell(0))
        dstNode.mkLink(0, 8, n1.createCell(0))
        dstNode.mkLink(8, 8, n2.createCell(0))
        dstNode.mkLink(16, 8, n3.createCell(0))

        g.setRegCell(r1, dstNode.createSymCell(PTASymOffset(0)))
        g.setRegCell(r2, stackC.node.createSymCell(PTASymOffset(3040)))

        val scalars = ScalarDomain()
        // memcpy(r1, r2, 24)
        scalars.setRegister(r3, ScalarValue.from(24UL))
        sbfLogger.warn {"Before memcpy(r1,r2,24) -> $g"}
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.warn {"After memcpy(r1,r2,24) -> $g"}

        val c1 = stackC.node.getSucc(PTAField(3030, 8))
        val c2 = stackC.node.getSucc(PTAField(3040, 8))
        val c3 = stackC.node.getSucc(PTAField(3048, 8))
        val c4 = stackC.node.getSucc(PTAField(3056, 8))
        Assertions.assertEquals(true,  c1 == c2 && c2 == c3 && c3 == c4 && c4 != null)
    }

    @Test
    fun test11() {
        sbfLogger.info { "====== TEST 11: memcpy from summarized to summarized =======" }
        /**
         * ```
         * dst = [(0,8) -> (n4,0), (8,8) -> (n5,0), (16,8) -> (n6,0)] ---> SummarizedNode -> (0, n7)
         * src = [(0,8) -> (n1,0), (8,8) -> (n2,0), (16,8) -> (n3,0)] ---> SummarizedNode -> (0, n8)
         *
         * after memcpy 24 bytes (it does not matter the number of bytes being copied)
         * src = dst = SummarizedNode -> (0, n9)
         * ```
         **/
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)

        // Create abstract state
        val absVal = MemoryDomain(PTANodeAllocator(),true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val srcNode = g.mkSummarizedNode()
        srcNode.setWrite()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
        val dstNode = g.mkSummarizedNode()

        val n4 = g.mkNode()
        n4.setWrite()
        val n5 = g.mkNode()
        n5.setWrite()
        val n6 = g.mkNode()
        n6.setWrite()

        dstNode.mkLink(0,  8, n4.createCell(0))
        dstNode.mkLink(8, 8, n5.createCell(0))
        dstNode.mkLink(16, 8, n6.createCell(0))

        stackC.node.mkLink(4040, 8, srcNode.createCell(0))
        srcNode.mkLink(0, 8, n1.createCell(0))
        srcNode.mkLink(8, 8, n2.createCell(0))
        srcNode.mkLink(16, 8, n3.createCell(0))

        g.setRegCell(r2, srcNode.createSymCell(PTASymOffset(0)))
        g.setRegCell(r1, dstNode.createSymCell(PTASymOffset(0)))

        val scalars = ScalarDomain()
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        scalars.setRegister(r3, ScalarValue.from(24UL))
        // memcpy(r1, r2, 24)
        sbfLogger.warn {"Before memcpy(r1,r2,24) -> $g"}
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.warn {"After memcpy(r1,r2,24) -> $g"}

        // It should unify the nodes pointed by src with those pointed by dst.
        Assertions.assertEquals(true, g.getRegCell(r1) == g.getRegCell(r2))
    }

    @Test
    fun test12() {
        sbfLogger.info { "====== TEST 12: memcpy with overlaps at destination =======" }
        /**
         * ```
         * dst = [(3036,8) -> _, (3040,8) -> _,  (3048,4) -> _, (3048,8) -> _, (3052,8) -> _, (3056,8) -> _ ]
         * src = [(4040,8) -> (n1,0), (4048,8) -> (n2,0), (4056,8) -> (n3,0)]
         *
         * after memcpy 24 bytes from 4040 to 3040:
         * dst = [(3040,8) -> (n1,0), (3048,8) -> (n2,0), (4056,8) -> (n3,0)]
         * ```
         * Moreover, the field `(3036,8)` is marked as top and thus, PTA throws an exception if the program accesses to it.
         * However, the fields `(3048, 4)` and `(3052,8)` are accessible so if the program accesses to them, PTA will
         * allocate fresh memory for them
         */

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        val absVal = MemoryDomain(PTANodeAllocator(),true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
        val n4 = g.mkNode()
        n4.setWrite()
        val n5 = g.mkNode()
        n5.setWrite()
        val n6 = g.mkNode()
        n6.setWrite()

        stackC.node.mkLink(3036, 8, n4.createCell(0))  /*1*/
        stackC.node.mkLink(3040, 8, n4.createCell(0))  /*2*/ // overlap 1 and 2
        stackC.node.mkLink(3048, 4, n5.createCell(0))  /*3*/
        stackC.node.mkLink(3048, 8, n5.createCell(0))  /*4*/ // overlap 3 and 4
        stackC.node.mkLink(3052, 8, n6.createCell(0))  /*5*/
        stackC.node.mkLink(3056, 8, n6.createCell(0))  /*6*/ // overlap 5 and 6


        stackC.node.mkLink(4040, 8, n1.createCell(0))
        stackC.node.mkLink(4048, 8, n2.createCell(0))
        stackC.node.mkLink(4056, 8, n3.createCell(0))
        g.setRegCell(r2, stackC.node.createSymCell(PTASymOffset(4040)))
        g.setRegCell(r1, stackC.node.createSymCell(PTASymOffset(3040)))

        val scalars = ScalarDomain()
        scalars.setRegister(r3, ScalarValue.from(24UL))

        sbfLogger.warn { "Before memcpy(r1,r2,24) -> $g" }
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.warn { "After memcpy(r1,r2,24) -> $g" }

        checkPointsToNode(g, r1, 0, 8, n1)
        checkPointsToNode(g, r1, 8, 8, n2)
        checkPointsToNode(g, r1, 16, 8, n3)

        // Check that we kill *all* overlapping cells at the destination
        var exception1 = false
        try {
            // (3036,8) was marked as top so the pointer domain should complain
            getNode(g, r1, (-4L).toShort(), 8)
        } catch (e: UnknownStackContentError) {
            exception1 = true
        }
        Assertions.assertEquals(true, exception1)

        // Check that there is fresh memory at (3052,8)
        val x = getNode(g, r1, 12, 8)
        Assertions.assertEquals(true, x != null && x.isUnaccessed())

        // Check that there is fresh memory at (3048,4)
        val y = getNode(g, r1, 8, 4)
        Assertions.assertEquals(true, y != null && y.isUnaccessed())
    }

    @Test
    fun test13() {
        sbfLogger.info { "====== TEST 13: memcpy from stack to (exact) non-stack with overlaps at destination =======" }
        /**
         * ```
         * src = [(3896,8) -> (n1,0), (3904,8) -> (n2,0),  (3912,8) -> (n3,0), (3920,8) -> (n4,0)]
         * dst = [(0,8) -> (n5,0)]

         *
         * after memcpy 32 bytes from src 3896 to dst at 4:
         * dst = [(4,8) -> (n1,0), (12,8) -> (n2,0), (20,8) -> (n3,0), (28,8) -> (n4,0)]
         * ```
         */

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        // Create abstract state
        val absVal = MemoryDomain(PTANodeAllocator(),true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val dstNode = g.mkNode()
        dstNode.setWrite()
        val n1 = g.mkIntegerNode()
        n1.setWrite()
        val n2 = g.mkIntegerNode()
        n2.setWrite()
        val n3 = g.mkIntegerNode()
        n3.setWrite()
        val n4 = g.mkIntegerNode()
        n4.setWrite()
        val n5 = g.mkIntegerNode()
        n5.setWrite()

        stackC.node.mkLink(3896, 8, n1.createCell(0))
        stackC.node.mkLink(3904, 8, n2.createCell(0))
        stackC.node.mkLink(3912, 8, n3.createCell(0))
        stackC.node.mkLink(3920, 8, n4.createCell(0))

        stackC.node.mkLink(4040, 8, dstNode.createCell(0))
        dstNode.mkLink(0, 8, n5.createCell(0))

        g.setRegCell(r1, dstNode.createSymCell(PTASymOffset(4)))
        g.setRegCell(r2, stackC.node.createSymCell(PTASymOffset(3896)))

        val scalars = ScalarDomain()
        // memcpy(r1, r2, 24)
        scalars.setRegister(r3, ScalarValue.from(32UL))
        sbfLogger.warn {"Before memcpy(r1,r2,24) -> $g"}
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.warn {"After memcpy(r1,r2,24) -> $g"}

        Assertions.assertEquals(true, getNode(g, r1, 0, 8) == n1)
        Assertions.assertEquals(true, getNode(g, r1, 8, 8) == n2)
        Assertions.assertEquals(true, getNode(g, r1, 16, 8) == n3)
        Assertions.assertEquals(true, getNode(g, r1, 24, 8) == n4)
        // memcpy cannot kill the content of r1-4 which corresponds to offset 0 and 8 bytes in dstNode
        // because the destination is not the stack and therefore we cannot perform a strong update.
        val x = getNode(g, r1, -4, 8)
        Assertions.assertEquals(true, x == n5)
    }


    @Test
    fun test14() {
        sbfLogger.info { "====== TEST 14: memcpy with overlaps at source (I) =======" }
        /**
         * ```
         * dst = [(3040,8 -> _, (3048,8) -> _, (3056,8) -> _]
         * src = [(4036,8) -> (n4,0), (4040,8) -> (n1,0), (4048,8) -> (n2,0), (4056,8) -> (n3,0), (4060,8) -> (n6,0) ]
         *
         * after memcpy 24 bytes from 4040 to 3040
         * dst = [(3040,8) -> (n1,0), (3048,8) -> (n2,0), (3056,8) -> (n3,0)]
         * ```
         */
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        val absVal = MemoryDomain(PTANodeAllocator(),true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
        val n4 = g.mkNode()
        n4.setWrite()
        val n5 = g.mkNode()
        n5.setWrite()
        val n6 = g.mkNode()
        n6.setWrite()


        stackC.node.mkLink(3040, 8, n4.createCell(0))
        stackC.node.mkLink(3048, 8, n5.createCell(0))
        stackC.node.mkLink(3056, 8, n6.createCell(0))


        stackC.node.mkLink(4036, 8, n4.createCell(0)) /*1*/
        stackC.node.mkLink(4040, 8, n1.createCell(0)) /*2*/ // overlap 1 and 2
        stackC.node.mkLink(4048, 8, n2.createCell(0)) /*3*/
        stackC.node.mkLink(4056, 8, n3.createCell(0)) /*4*/
        stackC.node.mkLink(4060, 8, n6.createCell(0)) /*5*/ // overlap 4 and 5

        g.setRegCell(r2, stackC.node.createSymCell(PTASymOffset(4040)))
        g.setRegCell(r1, stackC.node.createSymCell(PTASymOffset(3040)))

        val scalars = ScalarDomain()
        scalars.setRegister(r3, ScalarValue.from(24UL))

        sbfLogger.warn {"Before memcpy(r1,r2,24) -> $g"}
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.warn {"After memcpy(r1,r2,24) -> $g"}

        checkPointsToNode(g, r1, 0, 8, n1)
        checkPointsToNode(g, r1, 8, 8, n2)
        checkPointsToNode(g, r1, 16, 8, n3)

        // (4036,8) shouldn't be copied, so we shouldn't have anything at (3036,8)
        // (4060,8) shouldn't be copied, so we shouldn't have anything at (3060,8)
        // Note that since we haven't then accessed to offsets (3036 and 3060), the first time we access we will get fresh nodes.
        // Thus, the pointer analysis won't complain unlike test12, but we can check that (3036,8) and (3060,8) points to unaccessed nodes.
        val x = getNode(g, r1, (-4L).toShort(), 8) /* (3036,8) */
        Assertions.assertEquals(true, x != null && x.isUnaccessed())
        val y = getNode(g, r1, 20, 8)        /* (3060,8) */
        Assertions.assertEquals(true, y != null && y.isUnaccessed())

    }

    @Test
    fun test15() {
        sbfLogger.info { "====== TEST 15: memcpy with overlaps at source (II) =======" }
        /**
         * ```
         * dst = [(3040,8 -> _, (3048,8) -> _, (3056,8) -> _]
         * src = [(4040,8) -> (n1,0), (4048,4) -> (n2,0), (4048,8) -> (n2,0), (4056,8) -> (n3,0)]
         *
         * after memcpy 24 bytes from 4040 to 3040
         * dst = [(3040,8) -> (n1,0), (4048,4) -> (n2,0), (4048,8) -> (n2,0), (4056,8) -> (n3,0)]
         * ```
         */
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        val absVal = MemoryDomain(PTANodeAllocator(),true)
        val stackC = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stackC != null) { "memory domain cannot find the stack node" }
        stackC.node.setWrite()
        val g = absVal.getPTAGraph()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
        val n4 = g.mkNode()
        n4.setWrite()
        val n5 = g.mkNode()
        n5.setWrite()
        val n6 = g.mkNode()
        n6.setWrite()


        stackC.node.mkLink(3040, 8, n4.createCell(0))
        stackC.node.mkLink(3048, 8, n5.createCell(0))
        stackC.node.mkLink(3056, 8, n6.createCell(0))

        // At the source we have two overlapping cells at 4048. Both will be copied to the destination.
        stackC.node.mkLink(4040, 8, n1.createCell(0)) /*1*/
        stackC.node.mkLink(4048, 4, n2.createCell(0)) /*2*/
        stackC.node.mkLink(4048, 8, n2.createCell(0)) /*3*/ // overlap 2 and 3
        stackC.node.mkLink(4056, 8, n3.createCell(0)) /*4*/

        g.setRegCell(r2, stackC.node.createSymCell(PTASymOffset(4040)))
        g.setRegCell(r1, stackC.node.createSymCell(PTASymOffset(3040)))

        val scalars = ScalarDomain()
        scalars.setRegister(r3, ScalarValue.from(24UL))

        sbfLogger.warn {"Before memcpy(r1,r2,24) -> $g"}
        g.doMemcpy(scalars, newGlobalVariableMap())
        sbfLogger.warn {"After memcpy(r1,r2,24) -> $g"}

        checkPointsToNode(g, r1, 0, 8, n1)
        checkPointsToNode(g, r1, 8, 8, n2)
        checkPointsToNode(g, r1, 8, 4, n2)
        checkPointsToNode(g, r1, 16, 8, n3)
    }

}
