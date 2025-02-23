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

import kotlin.coroutines.*
import kotlinx.coroutines.*
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions.*
import parallel.ParallelPool
import utils.*
import java.util.concurrent.*

/**
    A long enough timeout to give the ParallelPool time to fully spin up, even in the CI environment - but not so long
    that our CI infrastructure will kill the test.
 */
const val LONG_TIMEOUT_SECONDS = 100L

class CoroutinesTest {
    @Test
    fun runsOnPool() {
        val pool = ParallelPool(1)

        runBlocking {
            pool.compute {
                ParallelPool.inherit(ParallelPool.SpawnPolicy.FAIL) {
                    assertSame(pool, it)
                }
            }
        }
    }

    @Test
    fun coroutineLimitsParallelism() {
        val pool = ParallelPool(2)
        val barrier = CyclicBarrier(3)
        val e = assertThrows(Exception::class.java) {
            runBlocking {
                pool.compute {
                    (1..3).map {
                        async {
                            barrier.await(100, TimeUnit.MILLISECONDS)
                        }
                    }.awaitAll()
                }
            }
        }
        assertTrue(e is TimeoutException || e is BrokenBarrierException)
    }

    @Test
    fun asyncForks() {
        val pool = ParallelPool(2)
        val barrier = CyclicBarrier(2)
        runBlocking {
            pool.compute {
                (1..2).map {
                    async {
                        barrier.await(LONG_TIMEOUT_SECONDS, TimeUnit.SECONDS)
                    }
                }.awaitAll()
            }
        }
    }

    class TestException : Exception()

    @Test
    fun exceptionInCoroutine() {
        val pool = ParallelPool(1)
        assertThrows(TestException::class.java) {
            runBlocking {
                pool.compute {
                    yield()
                    throw TestException()
                }
            }
        }
    }

    @Test
    fun ioDoesNotConsumeWorker() {
        val pool = ParallelPool(2)
        val barrier = CyclicBarrier(4)
        runBlocking {
            pool.compute {
                (1..4).map {
                    async {
                        pool.io {
                            barrier.await(LONG_TIMEOUT_SECONDS, TimeUnit.SECONDS)
                        }
                    }
                }.awaitAll()
            }
        }
    }

    @Test
    fun rpcConsumesWorker() {
        val pool = ParallelPool(2)
        val barrier = CyclicBarrier(4)
        val e = assertThrows(Exception::class.java) {
            runBlocking {
                pool.compute {
                    (1..4).map {
                        async {
                            pool.rpc {
                                // Try suspending the coroutine
                                yield()
                                // Try some managed blocking
                                ForkJoinPool.managedBlock(
                                    object : ForkJoinPool.ManagedBlocker {
                                        override fun isReleasable() = false
                                        override fun block() = barrier.await(100, TimeUnit.MILLISECONDS).let { true }
                                    }
                                )
                            }
                        }
                    }.awaitAll()
                }
            }
        }
        assertTrue(e is TimeoutException || e is BrokenBarrierException, "Wrong exception $e")
    }
}
