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
import sbf.callgraph.SolanaFunction
import sbf.cfg.*
import sbf.disassembler.*
import sbf.domains.*
import log.*
import org.junit.jupiter.api.Test
import java.io.ByteArrayOutputStream
import java.io.PrintStream
import org.junit.jupiter.api.*

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class MemoryMemsetTest {
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
    private fun getNode(
        g: PTAGraph,
        base: Value.Reg, offset: Short, width: Short
    ): PTANode? {
        val lhs = Value.Reg(SbfRegister.R7)
        check(base != lhs)
        val inst = SbfInstruction.Mem(Deref(width, base, offset, null), lhs, true, null)
        val locInst = LocatedSbfInstruction(Label.fresh(), 0, inst)
        g.doLoad(locInst, lhs, base, offset, width, SbfType.Top, newGlobalVariableMap())
        val sc = g.getRegCell(lhs)
        return sc?.node
    }

    // Return true if  *([baseR] + [offset]) points to [node]
    private fun checkPointsToNode(
        g: PTAGraph,
        base: Value.Reg, offset: Short,
        node: PTANode
    ) = getNode(g, base, offset, 8)?.id == node.id

    @Test
    fun test01() {
        sbfLogger.info { "====== TEST 1: memset on stack and known length =======" }

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
        g.setRegCell(r1, stackC.node.createSymCell(PTASymOffset(4040)))

        val scalars = ScalarDomain()
        scalars.setRegister(r2, ScalarValue.from(0UL))
        scalars.setRegister(r3, ScalarValue.from(24UL))
        val locInst = LocatedSbfInstruction(Label.Address(0), 0, SolanaFunction.toCallInst(SolanaFunction.SOL_MEMSET))
        sbfLogger.warn { "Before memset(r1,r2,24)\n$g" }
        g.doMemset(locInst, scalars, newGlobalVariableMap())
        sbfLogger.warn { "After\n$g" }

        Assertions.assertEquals(false, checkPointsToNode(g, r1, 0, n1))
        Assertions.assertEquals(false, checkPointsToNode(g, r1, 8, n2))
        Assertions.assertEquals(false, checkPointsToNode(g, r1, 16, n3))
    }

    @Test
    fun test02() {
        sbfLogger.info { "====== TEST 2: memset on stack and unknown length =======" }

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)

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
        g.setRegCell(r1, stackC.node.createSymCell(PTASymOffset(4040)))

        val scalars = ScalarDomain()
        scalars.setRegister(r2, ScalarValue.from(0UL))
        val locInst = LocatedSbfInstruction(Label.Address(0), 0, SolanaFunction.toCallInst(SolanaFunction.SOL_MEMSET))
        sbfLogger.warn { "Before memset(r1,r2,24)\n$g" }
        g.doMemset(locInst, scalars, newGlobalVariableMap())
        sbfLogger.warn { "After\n$g" }

        Assertions.assertEquals(true, checkPointsToNode(g, r1, 0, n1))
        Assertions.assertEquals(true, checkPointsToNode(g, r1, 8, n2))
        Assertions.assertEquals(true, checkPointsToNode(g, r1, 16, n3))
    }

    @Test
    fun test03() {
        sbfLogger.info { "====== TEST 2: memset on non-stack =======" }
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        // Create abstract state
        val absVal = MemoryDomain(PTANodeAllocator(), true)
        val g = absVal.getPTAGraph()
        val heapNode  = g.mkNode()
        heapNode.setWrite()
        val n1 = g.mkNode()
        n1.setWrite()
        val n2 = g.mkNode()
        n2.setWrite()
        val n3 = g.mkNode()
        n3.setWrite()
        heapNode.mkLink(0, 8, n1.createCell(0))
        heapNode.mkLink(8, 8, n2.createCell(0))
        heapNode.mkLink(16, 8, n3.createCell(0))
        g.setRegCell(r1, heapNode.createSymCell(PTASymOffset(0)))

        val scalars = ScalarDomain()
        scalars.setRegister(r2, ScalarValue.from(0UL))
        scalars.setRegister(r3, ScalarValue.from(24UL))
        val locInst = LocatedSbfInstruction(Label.Address(0), 0, SolanaFunction.toCallInst(SolanaFunction.SOL_MEMSET))
        sbfLogger.warn { "Before memset(r1,r2,24)\n$g" }
        g.doMemset(locInst, scalars, newGlobalVariableMap())
        sbfLogger.warn { "After\n$g" }

        Assertions.assertEquals(true, checkPointsToNode(g, r1, 0, n1))
        Assertions.assertEquals(true, checkPointsToNode(g, r1, 8, n2))
        Assertions.assertEquals(true, checkPointsToNode(g, r1, 16, n3))
    }

}
