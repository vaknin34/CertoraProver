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

abstract class SetBenchmark {
    @State(Scope.Benchmark)
    abstract class AddRemove(create: () -> MutableSet<HashTestObject>) {
        val set = create()
        val elems = Array<HashTestObject>(1000000) { HashTestObject(it, it) }
        val rand = Random(1234)
        var addObj: HashTestObject? = null
        var removeObj: HashTestObject? = null

        @Setup(Level.Invocation)
        fun pickObj() {
            addObj = elems[rand.nextInt(elems.size)]
            removeObj = if (rand.nextBoolean()) { elems[rand.nextInt(elems.size)] } else { null }
        }

        @Benchmark
        fun run() {
            if (removeObj != null) {
                set.remove(removeObj)
            }
            set.add(addObj!!)
        }


        open class ArrayHashSet : AddRemove(::ArrayHashSet)
        open class LinkedArrayHashSet : AddRemove(::LinkedArrayHashSet)
        open class HashSet : AddRemove(::HashSet)
        open class LinkedHashSet : AddRemove(::LinkedHashSet)
    }

    @State(Scope.Benchmark)
    abstract class AddMany(val create: () -> MutableSet<HashTestObject>) {
        lateinit var set: MutableSet<HashTestObject>
        val rand = Random(1234)
        val elems = Array<HashTestObject>(10000) {
            val r = rand.nextInt(10000)
            HashTestObject(r, r)
        }

        @Setup(Level.Invocation)
        fun init() { set = create() }

        @Benchmark
        fun run() {
            for (elem in elems) {
                set.add(elem)
            }
        }

        open class ArrayHashSet : AddMany(::ArrayHashSet)
        open class LinkedArrayHashSet : AddMany(::LinkedArrayHashSet)
        open class HashSet : AddMany(::HashSet)
        open class LinkedHashSet : AddMany(::LinkedHashSet)
    }
}
