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

package solver

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test

internal class CLIParserTest {
    @Test
    fun testValue() {
        // parses to a single value
        assertEquals("foo", CLIParser("foo").parse())
        assertEquals("foo:bar", CLIParser("foo:bar").parse())
        assertEquals("foo_bar", CLIParser("foo_bar").parse())
        assertEquals("foo-bar", CLIParser("foo-bar").parse())
        assertEquals("foo123", CLIParser("foo123").parse())
        assertEquals("foo:bar", CLIParser(" foo:bar ").parse())
        assertEquals("foo_bar", CLIParser(" foo_bar ").parse())
        assertEquals("foo-bar", CLIParser(" foo-bar ").parse())
        assertEquals("foo123", CLIParser(" foo123 ").parse())
        assertEquals("foo123 ", CLIParser(" 'foo123 ' ").parse())
        assertEquals("foo123 ", CLIParser(" \"foo123 \" ").parse())
    }

    @Test
    fun testList() {
        // parses to a list
        assertEquals(listOf<Any>(), CLIParser("[]").parse())
        assertEquals(listOf<Any>("foo"), CLIParser("[foo]").parse())
        assertEquals(listOf<Any>("foo", "bar"), CLIParser(" [foo,bar] ").parse())
        assertEquals(listOf<Any>("foo:bar", "foo-baz"), CLIParser("[ foo:bar , foo-baz ]").parse())
        assertEquals(listOf<Any>("--test=17", "foo-baz"), CLIParser("[ '--test=17' , foo-baz ]").parse())
        assertEquals(listOf<Any>("foo\"bar", "foo'bar"), CLIParser("['foo\"bar', \"foo'bar\"]").parse())
    }

    @Test
    fun testMap() {
        // parses to a map
        assertEquals(mapOf<String, Any>(), CLIParser("{}").parse())
        assertEquals(mapOf<String, Any>("foo" to "bar"), CLIParser("{foo=bar}").parse())
        assertEquals(mapOf<String, Any>("foo:6" to "5", "bar" to "baz"), CLIParser(" {foo:6= 5 , bar= baz } ").parse())
        assertEquals(
            mapOf<String, Any>("bar-15" to listOf<Any>("foo", "bar")),
            CLIParser("{bar-15=[foo, bar] }").parse()
        )
    }

    @Test
    fun testObject() {
        // parses to a map
        assertEquals("foo", CLIParser("foo").parse())
        assertEquals(Pair<Any, Map<String, Any>>("foo", mapOf("bar" to "5")), CLIParser("foo{bar=5}").parse())
        assertEquals(Pair<Any, Map<String, Any>>("foo", mapOf("bar" to "5")), CLIParser("foo { bar = 5 }").parse())
    }

    @Test
    fun testParsingError() {
        assertThrows(ConfigurationException::class.java) { CLIParser("[").parse() }
        assertThrows(ConfigurationException::class.java) { CLIParser("]").parse() }
        assertThrows(ConfigurationException::class.java) { CLIParser("foo,bar").parse() }
        assertThrows(ConfigurationException::class.java) { CLIParser("[foo,bar").parse() }
        assertThrows(ConfigurationException::class.java) { CLIParser("foo{bar=5").parse() }
        assertThrows(ConfigurationException::class.java) { CLIParser("bar=5}").parse() }
        assertThrows(ConfigurationException::class.java) { CLIParser("'foo'asd'").parse() }
    }
}
