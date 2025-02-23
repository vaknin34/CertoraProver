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

package parallel.coroutines

import kotlin.time.*
import kotlin.time.DurationUnit.*
import kotlinx.coroutines.*
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions.*
import parallel.ParallelPool
import utils.*
import java.util.concurrent.*
import kotlin.time.Duration.Companion.milliseconds

class RpcRaceTest {
    @Test
    fun oneResult() {
        val (winner, res) = runBlocking {
            with (ParallelPool()) {
                (1..3).rpcRace {
                    when (it) {
                        2 -> RaceFinish.Full("two")
                        else -> awaitCancellation()
                    }
                }
            }
        }
        assertEquals(1, winner)
        assertEquals(RacerResult.FromJob("two"), res[1])
        assertEquals(2, res.count { it is RacerResult.LostRace || it is RacerResult.Skipped })
    }

    @Test
    fun twoResultsRacing() {
        repeat(100) {
            val (winner, res) = runBlocking {
                with (ParallelPool()) {
                    (1..3).rpcRace {
                        when (it) {
                            1 -> RaceFinish.Full("one")
                            2 -> RaceFinish.Full("two")
                            else -> awaitCancellation()
                        }
                    }
                }
            }
            assertNotEquals(3, winner)
            val finished = res.count { it is RacerResult.FromJob }
            val lost = res.count { it is RacerResult.LostRace || it is RacerResult.Skipped }
            assertTrue(finished > 0, "$res")
            assertTrue(lost > 0, "$res")
            assertEquals(3, finished + lost, "$res")
        }
    }

    @Test
    fun timeout() {
        val (winner, res) = runBlocking {
            with (ParallelPool()) {
                (1..3).rpcRace(timeout = 100.toDuration(MILLISECONDS)) {
                    when (it) {
                        1 -> RaceFinish.DQF("one")
                        else -> awaitCancellation()
                    }
                }
            }
        }
        assertEquals(-1, winner)
        val expected = listOf(
            RacerResult.FromJob("one"),
            RacerResult.Timeout(null),
            RacerResult.Timeout(null)
        )
        assertEquals(expected, res)
    }

    @Test
    fun skipped() {
        val (winner, res) = runBlocking {
            with (ParallelPool(1)) {
                (1..3).rpcRace {
                    when(it) {
                        1 -> RaceFinish.Full("one")
                        2 -> RaceFinish.Full("two")
                        else -> RaceFinish.Full("three")
                    }
                }
            }
        }
        assertNotEquals(-1, winner)
        assertEquals(1, res.count { it is RacerResult.FromJob }, "$res")
        assertEquals(2, res.count { it is RacerResult.Skipped }, "$res")
    }

    @Test
    fun skippedDelayedAndTimeout() {
        val (winner, res) = runBlocking {
            with (ParallelPool(1)) {
                (1..3).rpcRace(
                    timeout = 100.milliseconds,
                    maximumAllowedDelay = 10.milliseconds,
                ) {
                    runInterruptible {
                        Thread.sleep(1000)
                        RaceFinish.Full("impossible")
                    }
                }
            }
        }
        assertEquals(-1, winner)
        assertEquals(1, res.count { it is RacerResult.Timeout }, "$res")
        assertEquals(2, res.count { it is RacerResult.SkippedDelayed }, "$res")
    }

    class TestException : Exception()

    @Test
    fun failure() {
        assertThrows(TestException::class.java) {
            runBlocking {
                with (ParallelPool()) {
                    (1..3).rpcRace<Int, Int> {
                        when(it) {
                            1 -> throw TestException()
                            else -> awaitCancellation()
                        }
                    }
                }
            }
        }
    }

    @Test
    fun ordering() {
        var current = 0
        runBlocking {
            with(ParallelPool(1)) {
                (1..1000).rpcRace {
                    assertEquals(++current, it)
                    RaceFinish.DQF(it)
                }
            }
        }
    }

    @Test
    fun jobsRunInParallel() {
        val barrier = CyclicBarrier(10)
        runBlocking {
            with (ParallelPool(10)) {
                (1..10).rpcRace {
                    barrier.await(LONG_TIMEOUT_SECONDS, TimeUnit.SECONDS)
                    RaceFinish.DQF(it)
                }
            }
        }
    }
}
