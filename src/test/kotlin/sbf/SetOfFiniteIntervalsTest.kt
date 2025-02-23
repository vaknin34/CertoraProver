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

import sbf.domains.*
import log.*
import org.junit.jupiter.api.*
import java.io.ByteArrayOutputStream
import java.io.PrintStream

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class SetOfFiniteIntervalsTest {
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
        val i1 = SetOfFiniteIntervals.new().add(FiniteInterval(4,8)).add(FiniteInterval(12,20))

        val x1 = FiniteInterval(2,6)
        val i2 = i1.add(x1)
        sbfLogger.warn{"Add $x1 in $i1 is $i2"}

        // [[2,8], [12,20]]
        Assertions.assertEquals(true, i2.size() == 2)
        Assertions.assertEquals(true, i2.contains(FiniteInterval(2,8)))
        Assertions.assertEquals(true, i2.contains(FiniteInterval(12,20)))

        val x2 = FiniteInterval(6,9)
        val i3 = i1.add(x2)
        sbfLogger.warn{"Add $x2 in $i1 is $i3"}

        // [[4,9], [12,20]]
        Assertions.assertEquals(true, i3.size() == 2)
        Assertions.assertEquals(true, i3.contains(FiniteInterval(4,9)))
        Assertions.assertEquals(true, i3.contains(FiniteInterval(12,20)))

        val x3 = FiniteInterval(2,14)
        val i4 = i1.add(x3)
        sbfLogger.warn{"Add $x3 in $i1 is $i4"}

        // [[2,20]]
        Assertions.assertEquals(true, i4.size() == 1)
        Assertions.assertEquals(true, i4.contains(FiniteInterval(2,20)))

        val x4 = FiniteInterval(9,22)
        val i5 = i1.add(x4)
        sbfLogger.warn{"Add $x4 in $i1 is $i5"}

        // [[4,22]]
        Assertions.assertEquals(true, i5.size() == 1)
        Assertions.assertEquals(true, i5.contains(FiniteInterval(4,22)))

        val x5 = FiniteInterval(2,22)
        val i6 = i1.add(x5)
        sbfLogger.warn{"Add $x5 in $i1 is $i6"}

        // [[2,22]]
        Assertions.assertEquals(true, i6.size() == 1)
        Assertions.assertEquals(true, i6.contains(FiniteInterval(2,22)))

    }

    @Test
    fun test02() {
        val i1 = SetOfFiniteIntervals.new()
            .add(FiniteInterval(10,14))
            .add(FiniteInterval(18,19))
            .add(FiniteInterval(20,30))

        val i2 = SetOfFiniteIntervals.new()
            .add(FiniteInterval(5,9))
            .add(FiniteInterval(10,12))
            .add(FiniteInterval(20,25))

        sbfLogger.warn{"i1=$i1 i2=$i2"}
        val i3 = i1.intersection(i2)
        sbfLogger.warn{"i3=intersection(i1,i2)=$i3"}

        Assertions.assertEquals(true, i3.size() == 2)
        Assertions.assertEquals(true, i3.contains(FiniteInterval(10,12)))
        Assertions.assertEquals(true, i3.contains(FiniteInterval(20,25)))
    }

    @Test
    fun test03() {
        val i1 = SetOfFiniteIntervals.new()
            .add(FiniteInterval(10,14))
            .add(FiniteInterval(30,50))

        val i2 = SetOfFiniteIntervals.new()
            .add(FiniteInterval(12,20))
            .add(FiniteInterval(32,40))
            .add(FiniteInterval(45,51))
            .add(FiniteInterval(53,60))

        sbfLogger.warn{"i1=$i1 i2=$i2"}
        val i3 = i1.intersection(i2)
        sbfLogger.warn{"i3=intersection(i1,i2)=$i3"}
        Assertions.assertEquals(true, i3.size() == 3)
        Assertions.assertEquals(true, i3.contains(FiniteInterval(12,14)))
        Assertions.assertEquals(true, i3.contains(FiniteInterval(32,40)))
        Assertions.assertEquals(true, i3.contains(FiniteInterval(45,50)))

    }

    @Test
    fun test04() {
        val i1 = SetOfFiniteIntervals.new()
            .add(FiniteInterval(14,16))
            .add(FiniteInterval(18,20))

        val i2 = SetOfFiniteIntervals.new()
            .add(FiniteInterval(12,14))
            .add(FiniteInterval(16,18))
            .add(FiniteInterval(20,22))


        sbfLogger.warn{"i1=$i1 i2=$i2"}
        val i3 = i1.intersection(i2)
        sbfLogger.warn{"i3=intersection(i1,i2)=$i3"}
        Assertions.assertEquals(true, i3.size() == 4)
        Assertions.assertEquals(true, i3.contains(FiniteInterval(14,14)))
        Assertions.assertEquals(true, i3.contains(FiniteInterval(16,16)))
        Assertions.assertEquals(true, i3.contains(FiniteInterval(18,18)))
        Assertions.assertEquals(true, i3.contains(FiniteInterval(20,20)))
    }

}
