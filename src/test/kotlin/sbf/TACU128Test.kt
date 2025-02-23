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

import config.ConfigScope
import datastructures.stdcollections.*
import sbf.cfg.*
import sbf.testing.SbfTestDSL
import log.*
import org.junit.jupiter.api.*
import java.io.ByteArrayOutputStream
import java.io.PrintStream

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class TACU128Test {
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

    /** 128-bits unsigned ceil division **/
    @Test
    fun test1() {
        val cfg = SbfTestDSL.makeCFG("test1") {
            bb(0) {
                r1 = r10
                BinOp.SUB(r1, 104)
                r2 = 3
                r3 = 0
                r4 = 2
                r5 = 0
                "CVT_u128_ceil_div"()
                r2 = r1[0]
                r3 = r1[8]
                assert(CondOp.EQ(r2, 2UL))
                assert(CondOp.EQ(r3, 0UL))
                exit()
            }
        }

        sbfLogger.warn{"$cfg"}
        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            val tacProg = toTAC(cfg)
            sbfLogger.warn { dumpTAC(tacProg) }
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

    /** 128-bits unsigned floor division **/
    @Test
    fun test2() {
        val cfg = SbfTestDSL.makeCFG("test2") {
            bb(0) {
                r1 = r10
                BinOp.SUB(r1, 104)
                r2 = 3
                r3 = 0
                r4 = 2
                r5 = 0
                "__udivti3"()
                r2 = r1[0]
                r3 = r1[8]
                assert(CondOp.EQ(r2, 1UL))
                assert(CondOp.EQ(r3, 0UL))
                exit()
            }
        }

        sbfLogger.warn{"$cfg"}
        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            val tacProg = toTAC(cfg)
            sbfLogger.warn { dumpTAC(tacProg) }
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

    /** 128-bits less or equal **/
    @Test
    fun test3() {
        val cfg = SbfTestDSL.makeCFG("test3") {
            bb(0) {
                r1 = 10
                r2 = 0
                r3 = 20
                r4 = 0
                "CVT_u128_leq"()
                assert(CondOp.EQ(r0, 1UL))
                exit()
            }
        }

        sbfLogger.warn{"$cfg"}
        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            val tacProg = toTAC(cfg)
            sbfLogger.warn { dumpTAC(tacProg) }
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

    /** 128-bits less or equal **/
    @Test
    fun test4() {
        val cfg = SbfTestDSL.makeCFG("test4") {
            bb(0) {
                r1 = 10
                r2 = 1
                r3 = 20
                r4 = 0
                "CVT_u128_leq"()
                assert(CondOp.EQ(r0, 0UL))
                exit()
            }
        }

        sbfLogger.warn{"$cfg"}
        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            val tacProg = toTAC(cfg)
            sbfLogger.warn { dumpTAC(tacProg) }
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

}
