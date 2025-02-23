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

import sbf.cfg.MutableSbfCFG
import sbf.disassembler.Label
import sbf.fixpoint.Wto
import sbf.fixpoint.WtoComponent
import sbf.fixpoint.WtoCycle
import sbf.fixpoint.WtoVertex
import log.*
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.io.ByteArrayOutputStream
import java.io.PrintStream
import org.junit.jupiter.api.*

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class WtoTest {
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
        val l1 = Label.Address(1)
        val l2 = Label.Address(2)
        val l3 = Label.Address(3)
        val l4 = Label.Address(4)
        val cfg = MutableSbfCFG("test1")
        val b1 = cfg.getOrInsertBlock(l1)
        val b2 = cfg.getOrInsertBlock(l2)
        val b3 = cfg.getOrInsertBlock(l3)
        val b4 = cfg.getOrInsertBlock(l4)
        cfg.setEntry(b1)
        b1.addSucc(b2)
        b2.addSucc(b3)
        b3.addSucc(b2)
        b2.addSucc(b4)
        val wto = Wto(cfg)

        val (one, twoThree, four) = wto.getComponents()
        Assertions.assertEquals(l1, one.expectLabel())
        twoThree.expectCycle {
            Assertions.assertEquals(listOf(l2, l3), it.expectLabels())
        }
        Assertions.assertEquals(l4, four.expectLabel())
    }

    @Test
    fun test02() {
        val l1 = Label.Address(1)
        val l2 = Label.Address(2)
        val l3 = Label.Address(3)
        val l4 = Label.Address(4)
        val l5 = Label.Address(5)
        val l6 = Label.Address(6)
        val l7 = Label.Address(7)
        val l8 = Label.Address(8)

        val cfg = MutableSbfCFG("test2")
        val b1 = cfg.getOrInsertBlock(l1)
        val b2 = cfg.getOrInsertBlock(l2)
        val b3 = cfg.getOrInsertBlock(l3)
        val b4 = cfg.getOrInsertBlock(l4)
        val b5 = cfg.getOrInsertBlock(l5)
        val b6 = cfg.getOrInsertBlock(l6)
        val b7 = cfg.getOrInsertBlock(l7)
        val b8 = cfg.getOrInsertBlock(l8)

        cfg.setEntry(b1)
        b1.addSucc(b2)
        b2.addSucc(b3)
        b2.addSucc(b8)
        b3.addSucc(b4)
        b4.addSucc(b5)
        b4.addSucc(b7)
        b5.addSucc(b6)
        b6.addSucc(b5)
        b6.addSucc(b7)
        b7.addSucc(b3)
        b7.addSucc(b8)
        val wto = Wto(cfg)
        sbfLogger.info {"$wto"}
        val (one, two, nest, eight) = wto.getComponents()
        Assertions.assertEquals(
            l1, one.expectLabel()
        )
        Assertions.assertEquals(
            l2, two.expectLabel()
        )
        nest.expectCycle<Unit> { (three, four, cycle, seven) ->
            Assertions.assertEquals(listOf(l3, l4, l7), listOf(three, four, seven).expectLabels())
            cycle.expectCycle {
                Assertions.assertEquals(listOf(l5, l6), it.expectLabels())
            }
        }
        Assertions.assertEquals(
            l8, eight.expectLabel()
        )

        Assertions.assertEquals(arrayListOf<Label>(), wto.nesting(Label.Address(1)).heads)
        Assertions.assertEquals(arrayListOf<Label>(),  wto.nesting(Label.Address(2)).heads)
        Assertions.assertEquals(arrayListOf<Label>(), wto.nesting(Label.Address(3)).heads)
        Assertions.assertEquals(arrayListOf(l3),  wto.nesting(Label.Address(4)).heads)
        Assertions.assertEquals(arrayListOf(l3), wto.nesting(Label.Address(5)).heads)
        Assertions.assertEquals(arrayListOf(l3,l5),  wto.nesting(Label.Address(6)).heads.asReversed())
        Assertions.assertEquals(arrayListOf(l3), wto.nesting(Label.Address(7)).heads)
        Assertions.assertEquals(arrayListOf<Label>(),  wto.nesting(Label.Address(8)).heads)


    }

    @Test
    fun test03() {
        val l1 = Label.Address(1)
        val l2 = Label.Address(2)
        val l3 = Label.Address(3)
        val l4 = Label.Address(4)
        val cfg = MutableSbfCFG("test3")
        val b1 = cfg.getOrInsertBlock(l1)
        val b2 = cfg.getOrInsertBlock(l2)
        val b3 = cfg.getOrInsertBlock(l3)
        val b4 = cfg.getOrInsertBlock(l4)
        cfg.setEntry(b1)
        b1.addSucc(b2)
        b2.addSucc(b3)
        b3.addSucc(b4)
        b4.addSucc(b2)
        b2.addSucc(b4)
        b1.addSucc(b3)
        val wto = Wto(cfg)
        val (one, twoThreeFour) = wto.getComponents()
        Assertions.assertEquals(l1, (one as? WtoVertex )?.label)
        Assertions.assertEquals(
            listOf(l2, l3, l4),
            twoThreeFour.expectCycle { it.expectLabels() },
        )
    }

}

private fun<R> WtoComponent.expectCycle(k: (List<WtoComponent>) -> R): R? {
    return (this as WtoCycle).getComponents().let(k)
}

private fun WtoComponent.expectLabel(): Label {
    return (this as WtoVertex).label
}

private fun List<WtoComponent>.expectLabels(): List<Label> {
    return this.map { it.expectLabel() }
}
