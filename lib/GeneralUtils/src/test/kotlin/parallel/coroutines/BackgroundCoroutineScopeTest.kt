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

@file:OptIn(ExperimentalCoroutinesApi::class)
package parallel.coroutines

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions.*
import kotlin.coroutines.*
import kotlin.time.Duration.Companion.milliseconds
import kotlinx.coroutines.*
import java.util.concurrent.*

@OptIn(DelicateCoroutinesApi::class)
class BackgroundCoroutineScopeTest {
    @Test
    fun throwsIfNotStarted() {
        val scope = BackgroundCoroutineScope()
        assertThrows(IllegalStateException::class.java) {
            scope.launch {
                fail("should not get here")
            }
        }
    }

    @Test
    fun usesSuppliedDispatcher() {
        val scope = BackgroundCoroutineScope()
        scope.run(newSingleThreadContext("single thread")) {
            scope.launch {
                assertTrue(Thread.currentThread().name.startsWith("single thread"))
            }
        }
    }

    @Test
    fun createsJob() {
        val scope = BackgroundCoroutineScope()
        scope.run(newSingleThreadContext("single thread")) {
            val scopeJob = scope.coroutineContext[Job]
            assertNotNull(scopeJob)
            scope.launch {
                val coroutineJob = coroutineContext[Job]
                assertNotNull(coroutineJob)
                assertTrue(coroutineJob in scopeJob!!.children)
            }
        }
    }

    @Test
    fun waitsForChild() {
        val scope = BackgroundCoroutineScope()
        var finished = false
        scope.run {
            scope.launch {
                Thread.sleep(10)
                finished = true
            }
        }
        assertTrue(finished)
    }

    @Test
    fun waitsForMultipleChildren() {
        val scope = BackgroundCoroutineScope()
        var finished1 = false
        var finished2 = false
        var finished3 = false
        scope.run {
            scope.launch {
                finished1 = true
            }
            scope.launch {
                Thread.sleep(10)
                finished2 = true
            }
            scope.launch {
                finished3 = true
            }
        }
        assertTrue(finished1) { "routine 1 didn't finish "}
        assertTrue(finished2) { "routine 2 didn't finish "}
        assertTrue(finished3) { "routine 3 didn't finish "}
    }

    @Test
    fun throwsOnError() {
        class FooException : Exception()
        val scope = BackgroundCoroutineScope()
        assertThrows(FooException::class.java) {
            scope.run {
                scope.launch {
                    throw FooException()
                }
            }
        }
    }

    @Test
    fun doesNotTimeOut() {
        val scope = BackgroundCoroutineScope()
        var finished = false
        scope.run(exitTimeout = 100000.milliseconds) {
            scope.launch {
                Thread.sleep(10)
                finished = true
            }
        }
        assertTrue(finished)
    }

    @Test
    fun timesOut() {
        val scope = BackgroundCoroutineScope()
        var finished = false
        scope.run(exitTimeout = 1.milliseconds) {
            scope.launch {
                Thread.sleep(1000)
                finished = true
            }
        }
        assertFalse(finished)
    }
}
