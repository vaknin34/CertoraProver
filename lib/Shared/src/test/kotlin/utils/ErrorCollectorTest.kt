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

package utils

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.DynamicTest.dynamicTest
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestFactory
import utils.CollectingResult.Companion.asError
import utils.CollectingResult.Companion.bind
import utils.CollectingResult.Companion.flatten
import utils.CollectingResult.Companion.lift
import utils.CollectingResult.Companion.ok
import utils.ErrorCollector.Companion.collectingErrors


@Suppress("UNREACHABLE_CODE")
class ErrorCollectorTest {

    /**
     * An example showing idiomatic use of [collectingErrors].  Does the same thing as [exampleWithoutCollector] (although
     * errors may be returned in a different order).
     */
    private fun exampleWithCollector(
        _x: CollectingResult<Int, String>,
        _y: CollectingResult<Boolean?, String>,
        _zs: List<CollectingResult<Int, String>>
    ): CollectingResult<Int, String> = collectingErrors {
        val x = bind(_x)
        val y = bind(_y) ?: returnError("y is null!")
        if (y && x in 3..5) {
            collectError("here's an error!")
            collectError("and another error")
        }
        collectAndFilter(_zs).forEach { z ->
            if (z > 10) {
                collectError("Big Z")
            }
        }
        return@collectingErrors x + 2
    }

    /**
     * An example showing why [collectingErrors] is useful.  Does the same thing as [exampleWithCollector] (although errors
     * may be returned in a different order).
     */
    private fun exampleWithoutCollector(
        _x: CollectingResult<Int, String>,
        _y: CollectingResult<Boolean?, String>,
        _zs: List<CollectingResult<Int, String>>
    ): CollectingResult<Int, String> {
        return _x.bind { x ->
            _y.bind { y ->
                if (y == null) {
                    "y is null!".asError()
                } else {
                    val errors = mutableListOf<String>()
                    if (y && x in 3..5) {
                        errors.add("here's an error!")
                        errors.add("and another error")
                    }
                    var hasErrors = errors.isNotEmpty()
                    _zs.map {
                        it.bind { z ->
                            if (z > 10) {
                                "Big Z".asError()
                            } else {
                                ok
                            }
                        }
                    }
                        .flatten()
                        .errorOrNull()?.let { hasErrors = true; errors.addAll(it) }
                    if (!hasErrors) {
                        (x + 2).lift()
                    } else {
                        errors.asError()
                    }
                }
            }
        }
    }

    /** Check that [exampleWithCollector] and [exampleWithoutCollector] return the same result up to a permutation of errors */
    private fun compareExamples(
        x : CollectingResult<Int,String>,
        y : CollectingResult<Boolean?,String>,
        zs : List<CollectingResult<Int,String>>
    ) : DynamicTest = dynamicTest("$x; $y; $zs") {
        val withCollector    = exampleWithCollector(x,y,zs)
        val withoutCollector = exampleWithoutCollector(x,y,zs)

        fun <R,E : Comparable<E>> sortErrors(x : CollectingResult<R,E>) = when(x) {
            is CollectingResult.Result<R> -> x
            is CollectingResult.Error<E>  -> x.messages.sorted().asError()
        }

        assert(sortErrors(withCollector) == sortErrors(withoutCollector)) { "different results with:\n  x = $x\n  y = $y\n  zs = $zs\nwith collector:\n  $withCollector\nwithout collector:\n  $withoutCollector" }
    }

    @TestFactory
    fun testExample() : List<DynamicTest> {
        var errorNum = 1
        fun errors(k : Int) = (0 until k).map { "error ${errorNum++}" }.asError()
        val xs = listOf(errors(0), errors(1), errors(2), 0.lift(), 4.lift())
        val ys = listOf(errors(1), errors(2), null.lift(), true.lift(), false.lift())
        val zs = listOf(errors(0), errors(2), 0.lift(), 20.lift())
        return sequence {
            xs.forEach { x ->
                ys.forEach { y ->
                    yield(compareExamples(x,y, emptyList()))
                    zs.flatMap { z1 ->
                        zs.map { z2 ->
                            yield(compareExamples(x,y,listOf(z1,z2)))
                        }
                    }
                }
            }
        }.toList()
    }

    // tests for specific functions //////////////////////////////////////////////////////////////////////////////

    /** Basic test that binding non-errors works */
    @Test fun testBindValue() {
        val _x = 0.lift()
        assertEquals(
            collectingErrors {
                val x = bind(_x)
                return@collectingErrors x
            },
            0.lift()
        )
    }

    /** Basic test that binding error values works */
    @Test fun testBindError() {
        val _y : CollectingResult<Int,String> = "error from y".asError()
        assertEquals(
            collectingErrors {
                collectError("error before")
                val y = bind(_y)
                collectError("error after")
                return@collectingErrors y
            },
            listOf("error before", "error from y").asError()
        )
    }

    @Test fun testReturnError() {
        assertEquals(
            collectingErrors {
                collectError("error before")
                returnError("returned error")
                collectError("error after")
            },
            listOf("error before", "returned error").asError()
        )
    }

    @Test fun testCollectError() {
        assertEquals(
            collectingErrors {
                collectError("added error")
            },
            listOf("added error").asError()
        )
    }

    /** Test addErrors on a non-empty list */
    @Test fun testCollectErrorsNonempty() {
        assertEquals(
            collectingErrors {
                collectErrors(listOf("error 1", "error 2"))
            },
            listOf("error 1", "error 2").asError()
        )
    }

    /** Test addErrors on an empty list */
    @Test fun testCollectErrorsEmpty() {
        assertEquals(
            collectingErrors {
                collectErrors(listOf<String>())
            },
            listOf<String>().asError()
        )
    }

    @Test fun testCollectWithError() {
        val _x : CollectingResult<Int,String> = "x error".asError()
        val _y = ok
        assertEquals(
            collectingErrors {
                collectError("error before")
                collect(_x.bind { ok }) // Note that `collect` only gets a `VoidResult` argument, so explicit mapping is needed. This is to make it clear that we may be losing information here.
                collectError("error between")
                collect(_y)
                collectError("error after")
            },
            listOf("error before", "x error", "error between", "error after").asError()
        )
    }

    /** Test [ErrorCollector.collectAndFilter] for [List] */
    @Test fun testListCollectAndFilter() {
        val items = listOf(
            "error 0".asError(),
            "good 1".lift(),
            "error 2".asError(),
            "good 3".lift()
        )
        assertEquals(
            collectingErrors {
                collectAndFilter(items).forEach { collectError("error for $it") }
            },
            listOf(
                "error 0",
                "error 2",
                "error for good 1",
                "error for good 3"
            ).asError()
        )
    }

    /** Test [ErrorCollector.collectAndFilter] for [Map] */
    @Test fun testMapBind() {
        val map = mapOf(
            "A" to "A error".asError(),
            "B" to 0.lift()
        )
        assertEquals(
            collectingErrors {
                collectError("good keys: ${collectAndFilter(map).keys}")
            },
            listOf("A error", "good keys: [B]").asError()
        )
    }
}
