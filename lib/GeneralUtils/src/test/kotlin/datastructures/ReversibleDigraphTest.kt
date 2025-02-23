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
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions.*

class ReversibleDigraphTest {

    @Test
    fun createFromGraph() {
        val map = mapOf(
            'a' to treapSetOf('b', 'c'),
            'b' to treapSetOf('c', 'd'),
            'd' to treapSetOf('a', 'e'),
            'f' to treapSetOf('d')
        )
        val fw = MutableReversibleDigraph(map)

        val succ = mapOf(
            'a' to treapSetOf('b', 'c'),
            'b' to treapSetOf('c', 'd'),
            'c' to treapSetOf<Char>(),
            'd' to treapSetOf('a', 'e'),
            'e' to treapSetOf<Char>(),
            'f' to treapSetOf('d')
        )

        val pred = mapOf(
            'a' to treapSetOf('d'),
            'b' to treapSetOf('a'),
            'c' to treapSetOf('a', 'b'),
            'd' to treapSetOf('b', 'f'),
            'e' to treapSetOf('d'),
            'f' to treapSetOf<Char>()
        )


        assertEquals(succ, fw)
        assertEquals(pred, fw.asReversed())
        assertEquals(succ, fw.asReversed().asReversed())
    }

    @Test
    fun put() {
        val fw = MutableReversibleDigraph<Char>()
        val rev = fw.asReversed()

        fw['a'] = treapSetOf('b', 'c')
        fw['b'] = treapSetOf('c', 'd')
        fw['d'] = treapSetOf('a')

        assertEquals(treapSetOf('b', 'c'), fw['a'])
        assertEquals(treapSetOf('c', 'd'), fw['b'])
        assertEquals(treapSetOf('a'), fw['d'])
        assertEquals(treapSetOf('d'), rev['a'])
        assertEquals(treapSetOf('a'), rev['b'])
        assertEquals(treapSetOf('a', 'b'), rev['c'])
        assertEquals(treapSetOf('b'), rev['d'])

        fw['b'] = treapSetOf('c', 'e')

        assertEquals(treapSetOf('c', 'e'), fw['b'])
        assertEquals(treapSetOf<Char>(), rev['d'])
        assertEquals(treapSetOf('b'), rev['e'])

        rev['c'] = treapSetOf('a', 'c', 'e')

        assertEquals(treapSetOf('a', 'c', 'e'), rev['c'])
        assertEquals(treapSetOf('b', 'c'), fw['a'])
        assertEquals(treapSetOf('c'), fw['c'])
        assertEquals(treapSetOf('c'), fw['e'])
    }

    @Test
    fun remove() {
        val map = mapOf(
            'a' to treapSetOf('b', 'c'),
            'b' to treapSetOf('a', 'd'),
            'c' to treapSetOf('c', 'd')
        )

        val fw = MutableReversibleDigraph(map)
        val rev = fw.asReversed()

        assertEquals(
            mapOf(
                'a' to treapSetOf('b', 'c'),
                'b' to treapSetOf('a', 'd'),
                'c' to treapSetOf('c', 'd'),
                'd' to treapSetOf<Char>()
            ),
            fw
        )
        assertEquals(
            mapOf(
                'd' to treapSetOf('b', 'c'),
                'c' to treapSetOf('c', 'a'),
                'b' to treapSetOf('a'),
                'a' to treapSetOf('b')
            ),
            rev
        )

        fw.remove('b')

        assertEquals(
            mapOf(
                'a' to treapSetOf('c'),
                'c' to treapSetOf('c', 'd'),
                'd' to treapSetOf<Char>()
            ),
            fw
        )
        assertEquals(
            mapOf(
                'd' to treapSetOf('c'),
                'c' to treapSetOf('c', 'a'),
                'a' to treapSetOf<Char>()
            ),
            rev
        )

        rev.remove('a')

        assertEquals(
            mapOf(
                'c' to treapSetOf('c', 'd'),
                'd' to treapSetOf<Char>()
            ),
            fw
        )
        assertEquals(
            mapOf(
                'd' to treapSetOf('c'),
                'c' to treapSetOf('c'),
            ),
            rev
        )

        fw.remove('c')

        assertEquals(
            mapOf(
                'd' to treapSetOf<Char>()
            ),
            fw
        )
        assertEquals(
            mapOf(
                'd' to treapSetOf<Char>()
            ),
            rev
        )

        rev.remove('d')

        assertEquals(
            mapOf<Char, Set<Char>>(),
            fw
        )
        assertEquals(
            mapOf<Char, Set<Char>>(),
            rev
        )
    }

    @Test
    fun iterate() {
        val succ = mapOf(
            'a' to treapSetOf('b', 'c'),
            'b' to treapSetOf('c', 'd'),
            'c' to treapSetOf<Char>(),
            'd' to treapSetOf('a')
        )

        val fw = MutableReversibleDigraph(succ)

        val entries = fw.entries.associate { (k, v) -> k to v }

        assertEquals(succ, entries)

        val it = fw.entries.iterator()
        while (it.hasNext()) {
            val entry = it.next()
            if (entry.key == 'b') {
                it.remove()
            }
        }

        val newSucc = mapOf(
            'a' to treapSetOf('c'),
            'c' to treapSetOf<Char>(),
            'd' to treapSetOf('a')
        )
        val newPred = mapOf(
            'a' to treapSetOf('d'),
            'c' to treapSetOf('a'),
            'd' to treapSetOf<Char>()
        )

        assertEquals(newSucc, fw)
        assertEquals(newPred, fw.asReversed())
    }
}
