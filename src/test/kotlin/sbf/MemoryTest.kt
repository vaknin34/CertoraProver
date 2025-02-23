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
import config.ConfigScope
import sbf.SolanaConfig.OptimisticPTAOverlaps
import sbf.cfg.*
import sbf.disassembler.SbfRegister
import sbf.disassembler.Label
import sbf.disassembler.newGlobalVariableMap
import sbf.domains.*
import log.*
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.io.ByteArrayOutputStream
import java.io.PrintStream
import org.junit.jupiter.api.*

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class MemoryTest {
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


    @Test
    fun test01() {
        sbfLogger.info { "====== TEST 1 =======" }

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        val absVal1 = MemoryDomain(PTANodeAllocator(), true)
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        stack1.node.setRead()
        val g1 = absVal1.getPTAGraph()
        val n1 = g1.mkNode()
        n1.setRead()
        val n2 = g1.mkNode()
        n2.setWrite()
        val n3 = g1.mkNode()
        n3.setWrite()
        val n4 = g1.mkNode()
        n4.setWrite()
        stack1.node.mkLink(4040, 4, n1.createCell(0))
        n1.mkLink(0, 4, n2.createCell(0))
        n1.mkLink(4, 4, n3.createCell(0))
        n1.mkLink(8, 4, n4.createCell(0))
        g1.setRegCell(r2, n2.createSymCell(PTASymOffset(0)))
        g1.setRegCell(r3, n3.createSymCell(PTASymOffset(0)))

        //printToFile("PTATest-01-1.dot", g1.toDot(false, "before"))

        ////////////////////

        val absVal2 = absVal1.deepCopy()
        sbfLogger.info { "absVal1=\n$absVal1" }
        sbfLogger.info { "absVal2=\n$absVal2" }

        val g2 = absVal2.getPTAGraph()
        val c2 = g2.getRegCell(r2)
        val c3 = g2.getRegCell(r3)
        check(c2 != null) { "cannot find cell for $r2" }
        check(c3 != null) { "cannot find cell for $r3" }
        c2.reify().unify(c3.reify())

        sbfLogger.info {
            "##After unifying ($n2,0) and ($n3, 0)##\n" +
                "absVal1=\n" +
                "$absVal1\n" +
                "absVal2=\n" +
                "$absVal2"
        }

        val check1 = absVal1.lessOrEqual(absVal2) && absVal2.lessOrEqual(absVal1)
        sbfLogger.info { "##Whether absVal1 == absVal2 --> res=$check1##" }

        Assertions.assertEquals(true, check1)

        val stack2 = absVal2.getRegCell(r10, newGlobalVariableMap())
        check(stack2 != null) { "memory domain cannot find the stack node" }

        val c4 = stack2.node.getSucc(PTAField(4040, 4))
        check(c4 != null) { "Stack at offset 4040 should have a link" }
        PTANode.smash(c4.node)

        sbfLogger.info {
            "##After collapsing the successor of the stack at offset 4040##\n" +
                "absVal1=\n" +
                "$absVal1\n" +
                "absVal2=\n" +
                "$absVal2"
        }

        val check2 = absVal1.lessOrEqual(absVal2) && absVal2.lessOrEqual(absVal1)
        sbfLogger.info { "##Whether absVal1 == absVal2 --> res=$check2##" }
        Assertions.assertEquals(true, check2)

        val n5 = g2.mkNode()
        n5.setWrite()
        g2.setRegCell(r3, n2.createSymCell(PTASymOffset(0)))
        val check3 = absVal1.lessOrEqual(absVal2) && absVal2.lessOrEqual(absVal1)
        sbfLogger.info { "##Whether absVal1 == absVal2 --> res=$check3##" }
        Assertions.assertEquals(false, check3)
    }

    @Test
    fun test2() {
        sbfLogger.info { "====== TEST 2 (JOIN)  =======" }
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)

        val absVal1 = MemoryDomain(PTANodeAllocator(), true)
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        stack1.node.setRead()
        val g1 = absVal1.getPTAGraph()
        val n1 = g1.mkNode()
        n1.setRead()
        val n2 = g1.mkNode()
        n2.setWrite()
        val n3 = g1.mkNode()
        n3.setWrite()
        val n4 = g1.mkNode()
        n4.setWrite()
        stack1.node.mkLink(4040, 4, n1.createCell(0))
        n1.mkLink(0, 4, n2.createCell(0))
        n1.mkLink(4, 4, n3.createCell(0))
        n1.mkLink(8, 4, n4.createCell(0))
        g1.setRegCell(r2, n2.createSymCell(PTASymOffset(0)))
        g1.setRegCell(r3, n3.createSymCell(PTASymOffset(0)))
        g1.setRegCell(r4, n4.createSymCell(PTASymOffset(0)))

        ////////////////////


        val absVal2 = absVal1.deepCopy()
        val absVal3 = absVal1.deepCopy()
        sbfLogger.info { "\nabsVal1=\n$absVal1" + "absVal2=\n$absVal2" + "absVal3=\n$absVal3" }

        //// AbsVal2
        val g2 = absVal2.getPTAGraph()
        val c2 = g2.getRegCell(r2)
        val c3 = g2.getRegCell(r3)
        check(c2 != null) { "cannot find cell for $r2 in AbsVal2" }
        check(c3 != null) { "cannot find cell for $r3 in AbsVal2" }
        c2.reify().unify(c3.reify())


        Assertions.assertEquals(true, (g1.getRegCell(r2) == g1.getRegCell(r3)))
        Assertions.assertEquals(true, (g2.getRegCell(r2) == g2.getRegCell(r3)))

        sbfLogger.info {
            "##After unifying $r2->$c2 and $r3->$c3 in absVal2##\n" +
                "absVal1=\n" +
                "$absVal1\n" +
                "absVal2=\n" +
                "$absVal2\n" +
                "absVal3=\n" +
                "$absVal3"
        }

        //// AbsVal3
        val g3 = absVal3.getPTAGraph()
        val c4 = g3.getRegCell(r3)
        val c5 = g3.getRegCell(r4)
        check(c4 != null) { "cannot find cell for $r3 in AbsVal3" }
        check(c5 != null) { "cannot find cell for $r4 in AbsVal3" }
        c4.reify().unify(c5.reify())

        sbfLogger.info {
            "##After unifying $r3->$c4 and $r4->$c5 in absVal3##\n" +
                "absVal1=\n" +
                "$absVal1\n" +
                "absVal2=\n" +
                "$absVal2\n" +
                "absVal3=\n" +
                "$absVal3"
        }


        Assertions.assertEquals(true, (g3.getRegCell(r2) == g3.getRegCell(r3)))
        Assertions.assertEquals(true, (g2.getRegCell(r2) == g2.getRegCell(r3)))
        Assertions.assertEquals(true, (g1.getRegCell(r2) == g1.getRegCell(r3)))
        Assertions.assertEquals(true, (g1.getRegCell(r3) == g1.getRegCell(r4)))
        Assertions.assertEquals(true, (g2.getRegCell(r3) == g2.getRegCell(r4)))
        Assertions.assertEquals(true, (g3.getRegCell(r3) == g3.getRegCell(r4)))


        /**
         * The join should do nothing since all changes took place on the shared graph between all the abstract states
         * so the join does nothing.
         */
        val absVal4 = absVal2.join(absVal3)
        sbfLogger.info {
            "##After AbsVal4 = join(AbsVal2, AbsVal3)##\n" +
                "absVal1=\n" +
                "$absVal1\n" +
                "absVal2=\n" +
                "$absVal2\n" +
                "absVal3=\n" +
                "$absVal3\n" +
                "absVal4=\n" +
                "$absVal4"
        }

        val g4 = absVal4.getPTAGraph()
        Assertions.assertEquals(true, (g3.getRegCell(r2) == g3.getRegCell(r3)))
        Assertions.assertEquals(true, (g2.getRegCell(r2) == g2.getRegCell(r3)))
        Assertions.assertEquals(true, (g1.getRegCell(r2) == g1.getRegCell(r3)))
        Assertions.assertEquals(true, (g1.getRegCell(r3) == g1.getRegCell(r4)))
        Assertions.assertEquals(true, (g2.getRegCell(r3) == g2.getRegCell(r4)))
        Assertions.assertEquals(true, (g3.getRegCell(r3) == g3.getRegCell(r4)))
        Assertions.assertEquals(true, (g4.getRegCell(r2) == g4.getRegCell(r3)))
        Assertions.assertEquals(true, (g4.getRegCell(r3) == g4.getRegCell(r4)))

    }

    @Test
    fun test3() {
        sbfLogger.info { "====== TEST 3 (JOIN) =======" }
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)

        val absVal1 = MemoryDomain(PTANodeAllocator(), true)
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        stack1.node.setRead()
        val g1 = absVal1.getPTAGraph()
        val n1 = g1.mkNode()
        n1.setRead()
        val n2 = g1.mkNode()
        n2.setWrite()
        val n3 = g1.mkNode()
        n3.setWrite()
        val n4 = g1.mkNode()
        n4.setWrite()
        stack1.node.mkLink(4040, 4, n1.createCell(0))
        n1.mkLink(0, 4, n2.createCell(0))
        n1.mkLink(4, 4, n3.createCell(0))
        n1.mkLink(8, 4, n4.createCell(0))
        g1.setRegCell(r2, n2.createSymCell(PTASymOffset(0)))
        g1.setRegCell(r3, n3.createSymCell(PTASymOffset(0)))
        g1.setRegCell(r4, n4.createSymCell(PTASymOffset(0)))


        ////////////////////
        val absVal2 = absVal1.deepCopy()
        val g2 = absVal2.getPTAGraph()
        // absVal2 = AbsVal1[r2 := r3]
        g2.setRegCell(r2, g2.getRegCell(r3))

        sbfLogger.info {
            "##After r2 := r3 on AbsVal2##\n" +
                "absVal1=\n" +
                "$absVal1\n" +
                "absVal2=\n" +
                "$absVal2"
        }
        ////////////////////

        val absVal3 = absVal1.join(absVal2)
        val g3 = absVal3.getPTAGraph()
        sbfLogger.info {
            "##After AbsVal3 = join(AbsVal1, AbsVal2)##\n" +
                "absVal1=\n" +
                "$absVal1\n" +
                "absVal2=\n" +
                "$absVal2\n" +
                "absVal3=\n" +
                "$absVal3"
        }
        // The join changes the shared nodes so the join also modifies g1 and g2
        Assertions.assertEquals(true, (g3.getRegCell(r2) == g3.getRegCell(r3)))
        Assertions.assertEquals(false, (g3.getRegCell(r2) == g3.getRegCell(r4)))
        Assertions.assertEquals(false, (g3.getRegCell(r3) == g3.getRegCell(r4)))
        Assertions.assertEquals(true, (g2.getRegCell(r2) == g2.getRegCell(r3)))
        Assertions.assertEquals(false, (g2.getRegCell(r2) == g2.getRegCell(r4)))
        Assertions.assertEquals(false, (g2.getRegCell(r3) == g2.getRegCell(r4)))
        Assertions.assertEquals(true, (g1.getRegCell(r2) == g1.getRegCell(r3)))
        Assertions.assertEquals(false, (g1.getRegCell(r2) == g1.getRegCell(r4)))
        Assertions.assertEquals(false, (g1.getRegCell(r3) == g1.getRegCell(r4)))

        g3.setRegCell(r2, g3.getRegCell(r4))
        // registers are flow-sensitive so a change in g3 should not affect other graphs (g1 and g2)
        Assertions.assertEquals(true, (g3.getRegCell(r2) == g3.getRegCell(r4)))
        Assertions.assertEquals(false, (g2.getRegCell(r2) == g2.getRegCell(r4)))
        Assertions.assertEquals(false, (g1.getRegCell(r2) == g1.getRegCell(r4)))

        sbfLogger.info {
            "##After r2:= r4##\n" +
                "absVal1=\n" +
                "$absVal1\n" +
                "absVal2=\n" +
                "$absVal2\n" +
                "absVal3=\n" +
                "$absVal3"
        }
    }

    //@Test
    /** This test is expected to throw an exception **/
    fun test4() {
        sbfLogger.info { "====== TEST 4 =======" }
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)


        val absVal1 = MemoryDomain(PTANodeAllocator(), true)
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        stack1.node.mkLink(0, 4, stack1.reify())

        val absVal2 = absVal1.deepCopy()
        val stack2 = absVal2.getRegCell(r10, newGlobalVariableMap())
        check(stack2 != null) { "memory domain cannot find the stack node" }
        sbfLogger.info {
            "\n" +
                "absVal1=\n" +
                "$absVal1\n" +
                "absVal2=\n" +
                "$absVal2"
        }

        PTANode.smash(stack1.node)

        sbfLogger.info {
            "##After smashing stack in AbsVal1##\n" +
                "absVal1=\n" +
                "$absVal1\n" +
                "absVal2=\n" +
                "$absVal2"
        }

        PTANode.smash(stack2.node)

        sbfLogger.info {
            "##After smashing stack in AbsVal2##\n" +
                "absVal1=\n" +
                "$absVal1\n" +
                "absVal2=\n" +
                "$absVal2"
        }
        val c1 = absVal2.getRegCell(r1, newGlobalVariableMap())
        check(c1 != null)
        val c2 = absVal2.getRegCell(r10, newGlobalVariableMap())
        check(c2 != null)
        c1.reify().unify(c2.reify())

        sbfLogger.info {
            "##After unifying r1 and r10 in AbsVal2##\n" +
                "absVal1=\n" +
                "$absVal1\n" +
                "absVal2=\n" +
                "$absVal2"
        }


        val absVal3 = absVal1.join(absVal2)
        sbfLogger.info {
            "##After absVal3 := join(absVal1, absVal2)##\n" +
                "absVal1=\n" +
                "$absVal1\n" +
                "absVal2=\n" +
                "$absVal2\n" +
                "absVal3=\n" +
                "$absVal3"
        }

        Assertions.assertEquals(true, absVal1.lessOrEqual(absVal3))
        Assertions.assertEquals(true, absVal2.lessOrEqual(absVal3))

    }

    @Test
    fun test5() {
        sbfLogger.info { "====== TEST 5 (JOIN) =======" }
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)

        val absVal1 = MemoryDomain(PTANodeAllocator(), true)
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        stack1.node.setRead()
        val g1 = absVal1.getPTAGraph()
        val n1 = g1.mkNode()
        n1.setRead()
        val n2 = g1.mkNode()
        n2.setWrite()
        val n3 = g1.mkNode()
        n3.setWrite()
        val n4 = g1.mkNode()
        n4.setWrite()
        val n5 = g1.mkNode()
        stack1.node.mkLink(4040, 4, n1.createCell(0))
        n1.mkLink(0, 4, n2.createCell(0))
        n1.mkLink(4, 4, n3.createCell(0))
        n1.mkLink(8, 4, n4.createCell(0))
        g1.setRegCell(r1, n1.createSymCell(PTASymOffset(0)))
        stack1.node.mkLink(4000, 4, n5.createCell(0))

        val absVal2 = absVal1.deepCopy()
        val g2 = absVal2.getPTAGraph()
        g2.setRegCell(r1, n5.createSymCell(PTASymOffset(0)))

        sbfLogger.info{"\nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        val absVal3 = absVal1.join(absVal2)
        sbfLogger.info{"absVal3 := join(absVal1, absVal2) --> \n$absVal3"}
        Assertions.assertEquals(true, absVal1.lessOrEqual(absVal3))
        Assertions.assertEquals(true, absVal2.lessOrEqual(absVal3))
    }

    @Test
    fun test6() {
        sbfLogger.info { "====== TEST 6 (JOIN) =======" }
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)

        val absVal1 = MemoryDomain(PTANodeAllocator(), true)
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        stack1.node.setRead()
        stack1.node.mkLink(4040, 4, stack1.node.createCell(4036))
        stack1.node.mkLink(4080, 4, stack1.node.createCell(4076))


        val absVal2 = absVal1.deepCopy()
        sbfLogger.info{"\nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        val absVal3 = absVal1.join(absVal2)
        sbfLogger.info{"absVal3 := join(absVal1, absVal2) --> \n$absVal3"}
        // The join does not lose precision
        Assertions.assertEquals(true, absVal1.lessOrEqual(absVal3))
        Assertions.assertEquals(true, absVal2.lessOrEqual(absVal3))
        Assertions.assertEquals(true, absVal3.lessOrEqual(absVal1))
        Assertions.assertEquals(true, absVal3.lessOrEqual(absVal2))
    }

    @Test
    fun test7() {
        sbfLogger.info { "====== TEST 7 (JOIN) =======" }
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)

        val nodeAllocator = PTANodeAllocator()

        val absVal1 = MemoryDomain(nodeAllocator, true)
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        stack1.node.setRead()
        stack1.node.mkLink(4040, 4, stack1.node.createCell(4036))
        stack1.node.mkLink(4080, 4, stack1.node.createCell(4076))


        val absVal2 = MemoryDomain(nodeAllocator, true)
        val stack2 = absVal2.getRegCell(r10, newGlobalVariableMap())
        check(stack2 != null) { "memory domain cannot find the stack node" }
        stack2.node.setRead()
        stack2.node.mkLink(4040, 4, stack2.node.createCell(4036))
        stack2.node.mkLink(4060, 4, stack2.node.createCell(4056))


        sbfLogger.info{"\nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        val absVal3 = absVal1.join(absVal2)

        sbfLogger.info{"AFTER JOIN \nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        sbfLogger.info{"absVal3 := join(absVal1, absVal2) --> \n$absVal3"}
        // The join strictly losses precision
        Assertions.assertEquals(true, absVal1.lessOrEqual(absVal3))
        Assertions.assertEquals(true, absVal2.lessOrEqual(absVal3))
        Assertions.assertEquals(false, absVal3.lessOrEqual(absVal1))
        Assertions.assertEquals(false, absVal3.lessOrEqual(absVal2))
    }

    @Test
    fun test8() {
        sbfLogger.info { "====== TEST 8 (JOIN) =======" }
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)

        val nodeAllocator = PTANodeAllocator()
        val absVal1 = MemoryDomain(nodeAllocator, true)
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        stack1.node.setRead()
        val g1 = absVal1.getPTAGraph()
        val n1 = g1.mkNode()  // Created by g1 but it will be shared by g2
        val n2 = g1.mkNode()
        g1.setRegCell(r1, n1.createSymCell(PTASymOffset(856)))
        g1.setRegCell(r2, n2.createSymCell(PTASymOffset(0)))

        val absVal2 = MemoryDomain(nodeAllocator, true)
        val stack2 = absVal2.getRegCell(r10, newGlobalVariableMap())
        check(stack2 != null) { "memory domain cannot find the stack node" }
        stack2.node.setRead()
        val g2 = absVal2.getPTAGraph()

        g2.setRegCell(r1, n1.createSymCell(PTASymOffset(872)))
        g2.setRegCell(r2, n1.createSymCell(PTASymOffset(872)))

        sbfLogger.info{"\nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        val absVal3 = absVal1.join(absVal2)
        sbfLogger.info{"absVal3 := join(absVal1, absVal2) --> \n$absVal3"}
        Assertions.assertEquals(true, absVal1.lessOrEqual(absVal3))
        Assertions.assertEquals(true, absVal2.lessOrEqual(absVal3))
    }

    @Test
    fun test9() {
        sbfLogger.info { "====== TEST 9 (UNIFY) =======" }

        val g = PTAGraph(PTANodeAllocator())
        val n1 = g.mkNode()
        val n2 = g.mkNode()
        val n3 = g.mkNode()
        val n4 = g.mkNode()

        n1.mkLink(0, 4, n2.createCell(0))
        n1.mkLink(4, 4, n2.createCell(8))
        n3.mkLink(0, 4, n2.createCell(4))
        n3.mkLink(4, 4, n4.createCell(0))
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        g.setRegCell(r1, n1.createSymCell(PTASymOffset(0)))
        g.setRegCell(r2, n3.createSymCell(PTASymOffset(4)))
        sbfLogger.info { "\nBefore unification:\n$g" }
        n1.unify(n3, 0, mutableMapOf())
        sbfLogger.info { "\nBefore unification (n1,0) and (n3,0):\n$g" }

        val c1 = g.getRegCell(r1)
        val c2 = g.getRegCell(r2)
        check(c1 != null && c2 != null)
        val f1 = PTAField(c1.offset.get()!!, 4)
        val f2 = PTAField(c2.offset.get()!!, 4)
        val res = c1.node.getSucc(f1) == c2.node.getSucc(f2)
        Assertions.assertEquals(true, res)
    }

    @Test
    fun test10() {
        sbfLogger.info { "====== TEST 10 (JOIN) =======" }
        // In this example, we unify one stack with a node from the other graph which is not the stack.
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r1 = Value.Reg(SbfRegister.R1_ARG)

        val nodeAllocator = PTANodeAllocator()

        val absVal1 = MemoryDomain(nodeAllocator, true)
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        stack1.node.setRead()
        val g1= absVal1.getPTAGraph()
        val n1 = g1.mkNode()
        val n1_f1 = g1.mkNode()
        val n1_f2 = g1.mkNode()
        stack1.node.mkLink(4096, 4, n1.createCell(0))
        n1.mkLink(0, 4, n1_f1.createCell(0))
        n1.mkLink(4, 4, n1_f2.createCell(0))
        g1.setRegCell(r1, stack1.node.createSymCell(PTASymOffset(8192)))


        val absVal2 = MemoryDomain(nodeAllocator, true)
        val stack2 = absVal2.getRegCell(r10, newGlobalVariableMap())
        check(stack2 != null) { "memory domain cannot find the stack node" }
        stack2.node.setRead()
        val g2 = absVal2.getPTAGraph()
        val n2 = g2.mkNode()
        val n2_f1 = g2.mkNode()
        val n2_f2 = g2.mkNode()
        stack2.node.mkLink(4096, 4, n2.createCell(0))
        n2.mkLink(0, 4, n2_f1.createCell(0))
        n2.mkLink(4, 4, n2_f2.createCell(0))
        g2.setRegCell(r1, n2.createSymCell(PTASymOffset(0)))

        sbfLogger.info{"\nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        val absVal3 = absVal1.join(absVal2)

        sbfLogger.info{"AFTER JOIN \nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        sbfLogger.info{"absVal3 := join(absVal1, absVal2) --> \n$absVal3"}
        Assertions.assertEquals(true, absVal1.lessOrEqual(absVal3))
        Assertions.assertEquals(true, absVal2.lessOrEqual(absVal3))

    }
    /* This test exercises when one of the stack is summarized.
       However, the pointer analysis is designed to avoid that, and throws an exception if it unexpectedly occurs.
       We disable the test to avoid throwing an exception.
     */
    fun test11() {
        sbfLogger.info { "====== TEST 11 (JOIN) =======" }
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)

        val nodeAllocator = PTANodeAllocator()

        val absVal1 = MemoryDomain(nodeAllocator, true)
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        stack1.node.setRead()
        val g1 = absVal1.getPTAGraph()
        val n1 = g1.mkSummarizedNode()
        n1.setRead()
        n1.setWrite()

        stack1.node.mkLink(4040, 4, n1.createCell(0))
        n1.mkLink(0, 4, n1.createCell(0))
        g1.setRegCell(r2, n1.createSymCell(PTASymOffset(0)))
        g1.setRegCell(r3, n1.createSymCell(PTASymOffset(0)))

        val absVal2 = MemoryDomain(nodeAllocator, true)
        val stack2 = absVal2.getRegCell(r10, newGlobalVariableMap())
        check(stack2 != null) { "memory domain cannot find the stack node" }
        stack2.node.setRead()
        stack2.node.setWrite()
        val smashedNode = PTANode.smash(stack2.node)
        smashedNode.mkLink(0, 4, smashedNode.createCell(0))
        val g2 = absVal2.getPTAGraph()
        g2.setRegCell(r10, smashedNode.createSymCell(PTASymOffset(0)))
        sbfLogger.info { "\nAbsVal1=$absVal1\nAbsVal2=$absVal2" }
        //val absVal3 = absVal1.join(absVal2)
        val absVal3 = absVal2.join(absVal1)

        sbfLogger.info { "AFTER JOIN \nAbsVal1=$absVal1\nAbsVal2=$absVal2" }
        sbfLogger.info { "absVal3 := join(absVal1, absVal2) --> \n$absVal3" }
        Assertions.assertEquals(true, absVal1.lessOrEqual(absVal3))
        Assertions.assertEquals(true, absVal2.lessOrEqual(absVal3))
    }

    // Check isWordCompatible function from PTACell
    @Test
    fun test12() {
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
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
        val n4 = g.mkNode()
        n4.setWrite()
        val n5 = g.mkNode()
        n5.setWrite()
        val n6 = g.mkNode()
        n6.setWrite()


        stackC.node.mkLink(3040, 8, n4.createCell(0))
        stackC.node.mkLink(3048, 8, n5.createCell(0))
        stackC.node.mkLink(3056, 8, n6.createCell(0))
        Assertions.assertEquals(true, stackC.node.createCell(3040).isWordCompatible(24, 8))
        Assertions.assertEquals(false, stackC.node.createCell(3040).isWordCompatible(24, 4))

        stackC.node.mkLink(4040, 8, n4.createCell(0))
        stackC.node.mkLink(4048, 4, n5.createCell(0))
        stackC.node.mkLink(4056, 8, n6.createCell(0))
        Assertions.assertEquals(false, stackC.node.createCell(4040).isWordCompatible(24, 8))

        ConfigScope(OptimisticPTAOverlaps, false).use {
            stackC.node.mkLink(4040, 8, n4.createCell(0))
            stackC.node.mkLink(4048, 4, n5.createCell(0))
            stackC.node.mkLink(4048, 8, n5.createCell(0))
            stackC.node.mkLink(4056, 8, n6.createCell(0))
            Assertions.assertEquals(false, stackC.node.createCell(4040).isWordCompatible(24, 8))
        }

        ConfigScope(OptimisticPTAOverlaps, true).use {
            stackC.node.mkLink(4040, 8, n4.createCell(0))
            stackC.node.mkLink(4048, 4, n5.createCell(0))
            stackC.node.mkLink(4048, 8, n5.createCell(0))
            stackC.node.mkLink(4056, 8, n6.createCell(0))
            Assertions.assertEquals(true, stackC.node.createCell(4040).isWordCompatible(24, 8))
        }
    }

    @Test
    fun test13() {
        sbfLogger.info { "====== TEST 13 (JOIN) =======" }
        /**
         * If OptimisticPTAJoin is disabled then join(X,Y) = top if X is a pointer but Y is a number
         */
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)

        val nodeAllocator = PTANodeAllocator()

        val absVal1 = MemoryDomain(nodeAllocator, true)
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        stack1.node.setRead()
        stack1.node.mkLink(4040, 4, stack1.node.createCell(4036))
        // R1 points to something that looks like a dangling pointer
        // Note that the pointer domain doesn't know anything about R1 but the scalar domain does
        absVal1.getScalars().setRegister(Value.Reg(SbfRegister.R1_ARG), ScalarValue(SbfType.NumType(ConstantNum(4))))
        absVal1.getPTAGraph().forget(Value.Reg(SbfRegister.R1_ARG))

        val absVal2 = MemoryDomain(nodeAllocator, true)
        val stack2 = absVal2.getRegCell(r10, newGlobalVariableMap())
        check(stack2 != null) { "memory domain cannot find the stack node" }
        stack2.node.setRead()
        stack2.node.mkLink(4040, 4, stack2.node.createCell(4036))
        // R1 points to (stack, 4040)
        absVal2.getPTAGraph().setRegCell(Value.Reg(SbfRegister.R1_ARG), stack2.node.createSymCell(Constant(4040)))

        sbfLogger.warn{"\nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        ConfigScope(SolanaConfig.OptimisticPTAJoin, false).use {
            val absVal3 = absVal1.join(absVal2)
            sbfLogger.warn{"absVal3 := join(absVal1, absVal2) --> \n$absVal3"}
            // We should lose track of R1
            Assertions.assertEquals(true, absVal3.getRegCell(Value.Reg(SbfRegister.R1_ARG), newGlobalVariableMap()) == null)
        }
    }

    @Test
    fun test14() {
        sbfLogger.info { "====== TEST 14 (JOIN) =======" }
        /**
         *  If OptimisticPTAJoin is enabled then join(X,Y) = X if X is a pointer and Y looks a dangling pointer.
         *  Using the scalar domain can know that Y is 4 (a small power-of-two)
         */
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)

        val nodeAllocator = PTANodeAllocator()

        val absVal1 = MemoryDomain(nodeAllocator, true)
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        stack1.node.setRead()
        stack1.node.mkLink(4040, 4, stack1.node.createCell(4036))
        absVal1.getPTAGraph().forget(Value.Reg(SbfRegister.R1_ARG))
        absVal1.getScalars().setRegister(Value.Reg(SbfRegister.R1_ARG), ScalarValue(SbfType.NumType(ConstantNum(4))))

        val absVal2 = MemoryDomain(nodeAllocator, true)
        val stack2 = absVal2.getRegCell(r10, newGlobalVariableMap())
        check(stack2 != null) { "memory domain cannot find the stack node" }
        stack2.node.setRead()
        stack2.node.mkLink(4040, 4, stack2.node.createCell(4036))
        // R1 points to (stack, 4040)
        absVal2.getPTAGraph().setRegCell(Value.Reg(SbfRegister.R1_ARG), stack2.node.createSymCell(Constant(4040)))
        absVal2.getScalars().setRegister(Value.Reg(SbfRegister.R1_ARG), ScalarValue(SbfType.PointerType.Stack(Constant(4040))))

        sbfLogger.warn{"\nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        ConfigScope(SolanaConfig.OptimisticPTAJoin, true).use {
            val absVal3 = absVal1.join(absVal2)
            sbfLogger.warn{"absVal3 := join(absVal1, absVal2) --> \n$absVal3"}
            val absVal4 = absVal2.join(absVal1)
            sbfLogger.warn{"absVal4 := join(absVal2, absVal1) --> \n$absVal4"}
            Assertions.assertEquals(true, absVal3.lessOrEqual(absVal4) && absVal4.lessOrEqual(absVal3))
            Assertions.assertEquals(true, absVal3.getRegCell(Value.Reg(SbfRegister.R1_ARG), newGlobalVariableMap()) != null)
        }
    }

    @Test
    fun test15() {
        sbfLogger.info { "====== TEST 15 (JOIN) =======" }
        /**
         *  If OptimisticPTAJoin is enabled then join(X,Y) = X if X is a pointer and Y is a number.
         *  The scalar domain doesn't know about Y but the pointer domain knows that Y points to a must-be-integer node.
         *
         *  This case should be treated in the same way that test14.
         */
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)

        val nodeAllocator = PTANodeAllocator()

        val absVal1 = MemoryDomain(nodeAllocator, true)
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        stack1.node.setRead()
        stack1.node.mkLink(4040, 4, stack1.node.createCell(4036))

        absVal1.getScalars().forget(Value.Reg(SbfRegister.R1_ARG))
        val integerNode = absVal1.getPTAGraph().mkIntegerNode()
        absVal1.getPTAGraph().setRegCell(Value.Reg(SbfRegister.R1_ARG), integerNode.createSymCell(Constant(0)))

        val absVal2 = MemoryDomain(nodeAllocator, true)
        val stack2 = absVal2.getRegCell(r10, newGlobalVariableMap())
        check(stack2 != null) { "memory domain cannot find the stack node" }
        stack2.node.setRead()
        stack2.node.mkLink(4040, 4, stack2.node.createCell(4036))
        // R1 points to (stack, 4040)
        absVal2.getPTAGraph().setRegCell(Value.Reg(SbfRegister.R1_ARG), stack2.node.createSymCell(Constant(4040)))
        absVal2.getScalars().setRegister(Value.Reg(SbfRegister.R1_ARG), ScalarValue(SbfType.PointerType.Stack(Constant(4040))))

        sbfLogger.warn{"\nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        ConfigScope(SolanaConfig.OptimisticPTAJoin, true).use {
            val absVal3 = absVal1.join(absVal2)
            sbfLogger.warn{"absVal3 := join(absVal1, absVal2) --> \n$absVal3"}
            val absVal4 = absVal2.join(absVal1)
            sbfLogger.warn{"absVal4 := join(absVal2, absVal1) --> \n$absVal4"}
            Assertions.assertEquals(true, absVal3.lessOrEqual(absVal4) && absVal4.lessOrEqual(absVal3))
            Assertions.assertEquals(true, absVal3.getRegCell(Value.Reg(SbfRegister.R1_ARG), newGlobalVariableMap()) != null)
        }
    }


    @Test
    fun test16() {
        sbfLogger.info { "====== TEST 16 pseudo-canonicalize =======" }
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val nodeAllocator = PTANodeAllocator()

        val absVal1 = MemoryDomain(nodeAllocator, true)
        val g1 = absVal1.getPTAGraph()
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        val n1 = g1.mkIntegerNode()
        val n2 = g1.mkIntegerNode()
        n1.setWrite()
        n2.setWrite()
        stack1.node.setRead()
        stack1.node.mkLink(4040, 4, n1.createCell(0))
        stack1.node.mkLink(4044, 4, n2.createCell(0))
        g1.setRegCell(Value.Reg(SbfRegister.R2_ARG), stack1.node.createSymCell(Constant(4040)))
        g1.setRegCell(Value.Reg(SbfRegister.R3_ARG), stack1.node.createSymCell(Constant(4044)))
        absVal1.getScalars().setStackContent(4040, 4,  ScalarValue(SbfType.NumType(ConstantNum(0))))
        absVal1.getScalars().setStackContent(4044, 4,  ScalarValue(SbfType.NumType(ConstantNum(0))))

        val absVal2 = MemoryDomain(nodeAllocator, true)
        val g2 = absVal2.getPTAGraph()
        val stack2 = absVal2.getRegCell(r10, newGlobalVariableMap())
        check(stack2 != null) { "memory domain cannot find the stack node" }
        val n3 = g2.mkIntegerNode()
        n3.setWrite()
        stack2.node.setRead()
        stack2.node.mkLink(4040, 8, n3.createCell(0))
        absVal2.getScalars().setStackContent(4040, 8,  ScalarValue(SbfType.NumType(ConstantNum(0))))


        sbfLogger.warn{"\nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        absVal1.pseudoCanonicalize(absVal2)
        absVal2.pseudoCanonicalize(absVal1)
        sbfLogger.warn{"After pseudo canonicalization\nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        //val oldVal = SolanaConfig.OptimisticPTAJoin.get()
        //SolanaConfig.OptimisticPTAJoin.set(false)
        //val absVal3 = absVal1.join(absVal2)
        //sbfLogger.warn{"absVal3 := join(absVal1, absVal2) --> \n$absVal3"}
        //SolanaConfig.OptimisticPTAJoin.set(oldVal)
        // We should lose track of R1
        //Assertions.assertEquals(true, absVal3.getRegCell(Value.Reg(SbfRegister.R1_ARG), mapOf()) == null)
    }

    @Test
    fun test17() {
        sbfLogger.info { "====== TEST 17 pseudo-canonicalize=======" }
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)

        val nodeAllocator = PTANodeAllocator()

        val absVal1 = MemoryDomain(nodeAllocator, true)
        val g1 = absVal1.getPTAGraph()
        val stack1 = absVal1.getRegCell(r10, newGlobalVariableMap())
        check(stack1 != null) { "memory domain cannot find the stack node" }
        val n1 = g1.mkIntegerNode()
        val n2 = g1.mkIntegerNode()
        n1.setWrite()
        n2.setWrite()
        stack1.node.setRead()
        stack1.node.mkLink(4040, 8, n1.createCell(0))
        g1.setRegCell(Value.Reg(SbfRegister.R2_ARG), stack1.node.createSymCell(Constant(4040)))
        absVal1.getScalars().setStackContent(4040, 8,  ScalarValue(SbfType.NumType(ConstantNum(0))))

        val absVal2 = MemoryDomain(nodeAllocator, true)
        val g2 = absVal2.getPTAGraph()
        val stack2 = absVal2.getRegCell(r10, newGlobalVariableMap())
        check(stack2 != null) { "memory domain cannot find the stack node" }
        val n3 = g2.mkIntegerNode()
        n3.setWrite()
        stack2.node.setRead()
        stack2.node.mkLink(4040, 4, n3.createCell(0))
        absVal2.getScalars().setStackContent(4040, 4,  ScalarValue(SbfType.NumType(ConstantNum(0))))

        sbfLogger.warn{"\nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        absVal1.pseudoCanonicalize(absVal2)
        absVal2.pseudoCanonicalize(absVal1)
        sbfLogger.warn{"After pseudo canonicalization\nAbsVal1=$absVal1\nAbsVal2=$absVal2"}
        //val oldVal = SolanaConfig.OptimisticPTAJoin.get()
        //SolanaConfig.OptimisticPTAJoin.set(false)
        //val absVal3 = absVal1.join(absVal2)
        //sbfLogger.warn{"absVal3 := join(absVal1, absVal2) --> \n$absVal3"}
        //SolanaConfig.OptimisticPTAJoin.set(oldVal)
        // We should lose track of R1
        //Assertions.assertEquals(true, absVal3.getRegCell(Value.Reg(SbfRegister.R1_ARG), mapOf()) == null)
    }

    @Test
    fun test18() {
        sbfLogger.info { "====== TEST 18 (SELECT) =======" }
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val nodeAllocator = PTANodeAllocator()
        val absVal = MemoryDomain(nodeAllocator, true)
        val g = absVal.getPTAGraph()
        val stack = absVal.getRegCell(r10, newGlobalVariableMap())
        check(stack != null) { "memory domain cannot find the stack node" }

        val n1 = g.mkNode()
        val n2 = g.mkNode()

        stack.node.setWrite()
        stack.node.mkLink(4040,8, n1.createCell(0))
        stack.node.mkLink(4048, 8, n2.createCell(0))
        g.setRegCell(r1, n1.createSymCell(PTASymOffset(0)))
        g.setRegCell(r2, n2.createSymCell(PTASymOffset(0)))
        sbfLogger.warn { "\nBefore select(r1, *, r1, r2):\n$g" }
        g.doSelect(LocatedSbfInstruction(Label.fresh(), 0, SbfInstruction.Select(r1, Condition(CondOp.EQ, Value.Reg(SbfRegister.R3_ARG), Value.Imm(0UL)), r1, r2)), newGlobalVariableMap(), ScalarDomain.makeTop())
        sbfLogger.warn { "\nAfter:\n$g" }

        run {
            val c1 = g.getRegCell(r1)
            val c2 = g.getRegCell(r2)
            check(c1 != null && c2 != null)
            val f1 = PTAField(c1.offset.get()!!, 8)
            val f2 = PTAField(c2.offset.get()!!, 8)
            Assertions.assertEquals(true, c1.node.getSucc(f1) == c2.node.getSucc(f2))
        }

        run {
            val c1 = stack.node.getSucc(PTAField(4040, 8))
            val c2 = stack.node.getSucc(PTAField(4048, 8))
            check(c1 != null && c2 != null)
            Assertions.assertEquals(true, c1 == c2)
        }
    }

}
