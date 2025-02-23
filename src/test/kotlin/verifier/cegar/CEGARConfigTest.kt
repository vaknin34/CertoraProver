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

package verifier.cegar

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import smt.CEGARConfig
import solver.*
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

class CEGARConfigTest {

    @Test
    fun testWorkerConfig() {
        assertEquals(
            CEGARConfig.WorkerConfig.default,
            CEGARConfig.WorkerConfig.z3
        )
        assertEquals(
            CEGARConfig.WorkerConfig.z3.liaConfig,
            SolverConfig.z3.def.copy(incremental = true)
        )
        assertEquals(
            CEGARConfig.WorkerConfig.cvc5.liaConfig.solverInfo,
            CVC5SolverInfo
        )
    }

    @Test
    fun testCEGARConfig() {
        assertEquals(CEGARConfig.default, CEGARConfig.def)
        assertTrue(CEGARConfig.default.workers.isNotEmpty())
        assertTrue(CEGARConfig.default.workers.contains(CEGARConfig.WorkerConfig.z3))
        assertTrue(CEGARConfig.default.niaWorkers.isNotEmpty())
    }

    @Test
    fun testParsing() {
        val wc1 = parseOne("cvc5", CEGARConfig.WorkerConfig.Converter())
        assertEquals(CEGARConfig.WorkerConfig.cvc5, wc1)
        val wc2 = parseOne("cvc5{learn=false}", CEGARConfig.WorkerConfig.Converter())
        assertEquals(CEGARConfig.WorkerConfig.cvc5.copy(learn = false), wc2)
        val wc3 = parseOne(
            "cvc5{learn=false,liaConfig=z3:def{incremental=true,preprocessorConfig=cvc5:nonlin}}",
            CEGARConfig.WorkerConfig.Converter()
        )
        assertEquals(
            CEGARConfig.WorkerConfig.cvc5.copy(
                learn = false,
                liaConfig = SolverConfig.z3.def.copy(incremental = true, preprocessorConfig = SolverConfig.cvc5.nonlin)
            ), wc3
        )

        try {
            SolverConfig("foo")
        } catch (e: ConfigurationException) {
            assertTrue(true)
        }

        val wc4 =
            parseOne("{name=foo,liaConfig=z3:def,niaConfig=cvc5:def,learn=true}", CEGARConfig.WorkerConfig.Converter())
        assertEquals(
            CEGARConfig.WorkerConfig(
                name = "foo",
                liaConfig = SolverConfig.z3.def,
                niaConfig = SolverConfig.cvc5.default,
                learn = true
            ),
            wc4
        )

        val cc1 = parseOne("def", CEGARConfig.Converter())
        assertEquals(CEGARConfig.def, cc1)
        val cc2 = parseOne("def{niaWorkers=[z3:def{randomSeed=17},cvc5:nonlin]}", CEGARConfig.Converter())
        assertEquals(
            CEGARConfig.def.copy(
                niaWorkers = listOf(
                    SolverConfig.z3.def.copy(randomSeed = 17),
                    SolverConfig.cvc5.nonlin
                )
            ),
            cc2
        )
        val cc3 = parseOne("{name=foo,timelimit=10s,workers=[z3],niaWorkers=[]}", CEGARConfig.Converter())
        assertEquals(
            CEGARConfig(
                name = "foo",
                timelimit = 10.seconds,
                workers = listOf(CEGARConfig.WorkerConfig.z3),
                niaWorkers = listOf()
            ),
            cc3
        )
    }
}
