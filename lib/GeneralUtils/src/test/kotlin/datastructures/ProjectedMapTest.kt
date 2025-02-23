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

import com.certora.collect.*
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

abstract class ProjectedMapTest {
    class ComparableKey(val wrapped: Int) : Comparable<ComparableKey> {
        override fun equals(other: Any?): Boolean {
            return other is ComparableKey && other.wrapped == this.wrapped
        }

        override fun hashCode(): Int {
            return wrapped % 4
        }

        override fun compareTo(other: ComparableKey): Int {
            return when {
                other.wrapped == this.wrapped -> 0
                this.wrapped < other.wrapped -> -1
                else -> 1
            }
        }

        override fun toString(): String {
            return "\$$wrapped"
        }
    }

    sealed class Hierarchy

    data class DualComponent(val componentOne: Int?, val componentTwo: Int?) : Hierarchy()
    data class Other(val v: Int) : Hierarchy()

    abstract fun makeMapOf() : TreapMap<ComparableKey, Hierarchy>

    @Test
    fun testProjection() {
        var m : TreapMap<ComparableKey, Hierarchy> = makeMapOf()
        for(i in 0..39) {
            if(i % 2 == 0) {
                m = m + (ComparableKey(i) to DualComponent(
                    i.takeIf { it % 3 == 0 },
                    i
                ))
            } else {
                m = m + (ComparableKey(i) to Other(i))
            }
        }
        var projectedMap = ProjectedMap(m, narrow = {
            it -> (it as? DualComponent)?.componentTwo
        }, merge = { curr, upd ->
            if(curr is Other) {
                curr
            } else if(curr == null) {
                if(upd == null) {
                    null
                } else {
                    DualComponent(null, upd)
                }
            } else {
                check(curr is DualComponent)
                if(upd == null && curr.componentOne == null) {
                    null
                } else {
                    curr.copy(componentTwo = upd)
                }
            }
        })
        Assertions.assertEquals(20, projectedMap.size)
        for(i in 0 .. 39) {
            if(i % 2 == 0) {
                Assertions.assertTrue(projectedMap.containsKey(ComparableKey(i)))
                Assertions.assertTrue(projectedMap.containsValue(i))
            } else {
                Assertions.assertFalse(projectedMap.containsKey(ComparableKey(i)))
                Assertions.assertFalse(projectedMap.containsValue(i))
            }
        }
        for(i in 0 .. 39) {
            if(i % 2 == 1 && i % 3 == 0) {
                projectedMap -= ComparableKey(i) // this is a no-op, removing a mapping for "Other"
            } else if(i % 2 == 1) {
                projectedMap += (ComparableKey(i) to i) // also a no-op, cannot overwrite mapping for Other
            } else if(i % 4 == 0 && i % 3 == 0) { // this will null out componentTwo for keys 12 and 24 (but these keys will remain in the map)
                projectedMap -= ComparableKey(i)
            } else if(i % 5 == 0) {
                projectedMap += (ComparableKey(i) to i + 1) // update componentTwo "in place" for those keys 10 and 20 and 30
            } else if(i % 3 == 2) {
                projectedMap -= ComparableKey(i) // remove mappings where componentTwo and one are now both null
            } else if(i % 3 == 1) {
                projectedMap += (ComparableKey(i) to i - 1)
            }
        }
        for(i in 40 .. 44) {
            projectedMap += (ComparableKey(i) to i) // fresh bindings
        }
        val wrapped = projectedMap.wrapped
        for(i in 0 .. 39) {
            if(i % 2 == 1) {
                Assertions.assertEquals(Other(i), wrapped.get(ComparableKey(i)))
                continue
            }
            if(i % 3 == 0 && i % 4 == 0) {
                Assertions.assertEquals(DualComponent(i, null), wrapped.get(ComparableKey(i)))
            } else if(i % 5 == 0) {
                val expected = DualComponent(i.takeIf { i % 3 == 0 }, i + 1)
                Assertions.assertEquals(expected, wrapped.get(ComparableKey(i)))
            } else if(i % 3 == 2) {
                Assertions.assertEquals(null, wrapped.get(ComparableKey(i)))
            } else if(i % 3 == 1) {
                Assertions.assertEquals(DualComponent(null, i - 1), wrapped.get(ComparableKey(i)))
            }
        }
        for(i in 40 .. 44) {
            Assertions.assertEquals(DualComponent(null, i), wrapped.get(ComparableKey(i)))
        }
    }
}
