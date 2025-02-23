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

package datastructures

import org.openjdk.jmh.annotations.*
import java.util.Random
import java.util.concurrent.TimeUnit
import java.util.HashSet
import java.util.LinkedHashSet
import kotlinx.collections.immutable.*
import utils.*

abstract class MapBenchmark {
    @State(Scope.Benchmark)
    abstract class AddRemove(create: () -> MutableMap<HashTestObject?, Any?>) {
        val map = create()
        val elems = Array<HashTestObject>(1000000) { HashTestObject(it, it) }
        val rand = Random(1234)
        var addObj: HashTestObject? = null
        var removeObj: HashTestObject? = null
        val valueObj = Object()

        @Setup(Level.Invocation)
        fun pickObj() {
            addObj = elems[rand.nextInt(elems.size)]
            removeObj = if (rand.nextBoolean()) { elems[rand.nextInt(elems.size)] } else { null }
        }

        @Benchmark
        fun run() {
            if (removeObj != null)
                map.remove(removeObj)
            map.put(addObj, valueObj)
        }

        open class ArrayHashMap : AddRemove(::ArrayHashMap)
        open class LinkedArrayHashMap : AddRemove(::LinkedArrayHashMap)
        open class HashMap : AddRemove(::HashMap)
        open class LinkedHashMap : AddRemove(::LinkedHashMap)
    }


    @State(Scope.Benchmark)
    abstract class AddMany(val create: () -> MutableMap<HashTestObject?, Any?>) {
        lateinit var map: MutableMap<HashTestObject?, Any?>
        val rand = Random(1234)
        val elems = Array<HashTestObject>(10000) {
            val r = rand.nextInt()
            HashTestObject(r, r)
        }
        val valueObj = Object()

        @Setup(Level.Invocation)
        fun init() { map = create() }

        @Benchmark
        fun run() {
            for (elem in elems) {
                map.put(elem, valueObj)
            }
        }

        open class ArrayHashMap : AddMany(::ArrayHashMap)
        open class LinkedArrayHashMap : AddMany(::LinkedArrayHashMap)
        open class HashMap : AddMany(::HashMap)
        open class LinkedHashMap : AddMany(::LinkedHashMap)
    }
}
