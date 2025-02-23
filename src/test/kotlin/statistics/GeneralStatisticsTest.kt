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

package statistics

import kotlinx.serialization.Serializable
import kotlinx.serialization.encodeToString
import kotlinx.serialization.json.Json
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows
import verifier.*
import kotlin.time.Duration.Companion.seconds
import java.io.Serializable as JavaSerializable

class GeneralStatisticsTest {

    class ResultParser(val input: String) {
        var c = 0
        fun stringToJsonKey(tok: String) = "\"$tok\":"
        fun skipWhiteSpace() {
            while (c < input.length && input[c].isWhitespace()) ++ c
        }
        fun readToken(tok: String): Boolean {
            val stopIndex = c + tok.length
            if (stopIndex < input.length) {
                val s = input.substring(c, c + tok.length)
                if (s == tok) {
                    c += tok.length
                    return true;
                }
            }
            return false;
        }

        fun readBalancedBraces() : Pair<String, Boolean> {
            val startIndex = c
            if (! readToken("{")) return "" to false
            var numBraces = 1
            while (c < input.length && numBraces > 0) {
                if (input[c] == '{') ++ numBraces
                else if (input[c] == '}') -- numBraces
                ++ c
            }
            return if (c == input.length) "" to false
            else input.substring(startIndex, c) to true
        }
        fun parseEnvelope(key1: String, key2: String) : Boolean {
            skipWhiteSpace()
            if (!readToken("{")) return false
            skipWhiteSpace()
            if (!readToken(stringToJsonKey(key1))) return false
            skipWhiteSpace()
            if (!readToken("{")) return false
            skipWhiteSpace()
            if (! readToken(stringToJsonKey(key2))) return false
            skipWhiteSpace()
            return true
        }


        private fun parseMultipleResults(key1: String, key2: String) : List<Pair<String, Boolean>> {
            val results = mutableListOf<Pair<String, Boolean>>()
            if (!parseEnvelope(key1, key2) || input[c++] != '[') {
                return listOf("" to false)
            } else {
                while (c < input.length && input[c] != ']') {
                    // To make sure we progress
                    val prev_c = c
                    results.add(readBalancedBraces())
                    if (readToken(",")) {
                        skipWhiteSpace()
                    }
                    check(c > prev_c) {"Infinite loop in checking input"}
                }
            }
            return results
        }
        fun parseStatsResults() = parseMultipleResults(SMTStatsResource.smtSpaceString, SMTStatsResource.vcSpaceString)
        fun parseSolverVersionResults() = parseMultipleResults(SMTStatsResource.smtSpaceString, SMTStatsResource.solverVersionString)
    }

    @Serializable
    class A(val v: String, val i: Int) : JavaSerializable { override fun toString(): String = Json.encodeToString(arrayOf(this)) }

    @Test
    fun recordAnyTest() {

        val collector = EnabledSDCollector()

        collector.recordAny(A("a", 0), "key2", "key1")

        assertDoesNotThrow { collector.getAsString() }
    }

    @Test
    fun smtLoggerTest() {

        val collector = EnabledSDCollector()

        val statistics = SMTStatistics(
            NameObject("base"),
            23.seconds,
        )

        SMTStatsResource(SMTStatsHolder(statistics), collector).close()
        val output = collector.getAsString()
        val results = ResultParser(output).parseStatsResults()
        assert(results.size == 1)
        val (jsonDescr, success) = results[0]
        assertTrue(success)
        val o = Json.decodeFromString<SMTStatistics>(jsonDescr)

        assertEquals(o, statistics)

        // Should fail:
        assertThrows<IllegalArgumentException> {
            Json.decodeFromString<SMTStatistics>(output)
        }
    }
    @Test
    fun versionTest() {
        val collector = EnabledSDCollector()
        val versions = listOf(
            SolverVersion(
                "solver",
                "exec",
                "1.4",
            ),
            SolverVersion(
                "solver2",
                "exec2",
                null,
            )
        )

        versions.forEach {
            collector.recordAny(
                SolverVersionJavaSerializerWrapper(it),
                tag = SMTStatsResource.solverVersionString,
                key = SMTStatsResource.smtSpaceString
            )
        }
        val output2 = collector.getAsString()
        val results2 = ResultParser(output2).parseSolverVersionResults()
        assert(results2.size == versions.size)

        versions.forEachIndexed { idx, solver ->
            val (versionDescr, ok) = results2[idx]
            assertTrue(ok)
            val decodedSolver = Json.decodeFromString<SolverVersion>(versionDescr)
            assertEquals(decodedSolver, solver)
        }
    }

    @Test
    fun multipleLogsTest() {
        val collector = EnabledSDCollector()

        listOf(
            SMTStatistics(
                NameObject("base1", listOf("type1")),
                23.seconds,
            ),
            SMTStatistics(
                NameObject("base2", listOf("type2")),
                23.seconds,
            )
        ).forEach {
            SMTStatsResource(SMTStatsHolder(it), collector).close()
        }
        val output = collector.getAsString()
        ResultParser(output).parseStatsResults().forEach {
            val (_, success) = it
            assertTrue(success)
        }
    }
}
