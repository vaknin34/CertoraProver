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

import ksp.dynamicconversion.DynamicConversionProvider
import org.junit.jupiter.api.Test
import ksp.dynamicconversion.*
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.api.Assertions.*

@AddDynamicConversion
data class BaseConfig(
    val name: String,
    val randomSeed: Int,
) {
    class Converter: DynamicConverter<BaseConfig> {
        override fun invoke(v: Any) = getConfig(v.toString())
    }
    companion object {
        fun getConfig(name: String) = BaseConfig(name, -1)
    }
}

@AddDynamicConversion
data class NestedConfig(
    val name: String,
    @ConvertibleWith(BaseConfig.Converter::class)
    val lia: BaseConfig,
) {
    companion object {
        fun getConfig(name: String) = NestedConfig(name, BaseConfig("lia", 1))
    }
}

@AddDynamicConversion
data class WithLists(
    val strs: List<String>,
    val ints: List<Int> = listOf(),
    @ConvertibleWith(BaseConfig.Converter::class)
    val confs: List<BaseConfig> = listOf(),
) {
    companion object {
        fun getConfig() = WithLists(listOf("foo", "bar"))
    }
}

/**
 * Some unit tests for [DynamicConversionProvider] and [DynamicConversionProcessor].
 * As it relies on Ksp, we use a library to compile code during the test.
 */
class DynamicConversionTest {
    @Test
    /**
     * Tests dynamic copy with a basic data class. Override some properties
     * and check basic type conversion.
     */
    fun testBasic() {
        val sc = BaseConfig.getConfig("test")
        val sc2 = sc.copy(mapOf("name" to "foo"))
        assertEquals("foo", sc2.name)
        val sc3 = sc.copy(mapOf("randomSeed" to "-5"))
        assertEquals(-5, sc3.randomSeed)
        val sc4 = BaseConfig.constructFrom(mapOf("name" to "test", "randomSeed" to "17"))
        assertEquals("test", sc4.name)
        assertEquals(17, sc4.randomSeed)
    }

    @Test
    /**
     * Tests dynamic copy with a recursive data class: it has members of custom
     * types and provides custom converters to these types.
     */
    fun testRecursive() {
        val cc = NestedConfig.getConfig("test")
        val cc2 = cc.copy(mapOf("name" to "foo"))
        assertEquals("foo", cc2.name)
        val cc3 = cc.copy(mapOf("lia" to "newlia"))
        assertEquals(BaseConfig("newlia", -1), cc3.lia)
        val cc4 = cc.copy(mapOf("lia" to BaseConfig("newnia", 27)))
        assertEquals(BaseConfig("newnia", 27), cc4.lia)
        val cc5 = NestedConfig.constructFrom(mapOf("name" to "test", "lia" to cc.lia))
        assertEquals("test", cc5.name)
        assertEquals(cc.lia, cc5.lia)
    }

    @Test
    /**
     * Tests whether we can properly deal with lists.
     */
    fun testLists() {
        val wl = WithLists.getConfig()
        val wl2 = wl.copy(mapOf("strs" to listOf("baz")))
        assertEquals(listOf("baz"), wl2.strs)
        val wl3 = wl.copy(mapOf("ints" to listOf("1", 2, "3")))
        assertEquals(listOf(1,2,3), wl3.ints)
        val wl4 = wl.copy(mapOf("confs" to listOf("foo", "bar")))
        assertEquals(listOf(BaseConfig.getConfig("foo"), BaseConfig.getConfig("bar")), wl4.confs)
        val wl5 = WithLists.constructFrom(mapOf(
            "strs" to listOf("foo", "bar"),
            "ints" to listOf("15", "-123"),
            "confs" to listOf("baz", BaseConfig.getConfig("blub"))
        ))
        assertEquals(listOf("foo", "bar"), wl5.strs)
        assertEquals(listOf(15, -123), wl5.ints)
        assertEquals(listOf(BaseConfig.getConfig("baz"), BaseConfig.getConfig("blub")), wl5.confs)
    }

    @Test
    /**
     * Tests that we properly handle non-existing keys (by throwing an exception)
     * or ill-typed values.
     */
    fun testInvalid() {
        val cc = NestedConfig.getConfig("test")
        assertEquals("Unknown property \"foobar\" for utils.NestedConfig",
            assertThrows<DynamicConversionException>  {
                cc.copy(mapOf("foobar" to "baz"))
            }.message)

        assertEquals("Mandatory constructor argument \"name\" for utils.NestedConfig is missing",
            assertThrows<DynamicConversionException> {
                NestedConfig.constructFrom(mapOf("lia" to cc.lia))
            }.message)

        assertEquals("Unknown property \"nametypo\" for utils.NestedConfig",
            assertThrows<DynamicConversionException> {
                NestedConfig.constructFrom(mapOf("name" to "foo", "nametypo" to "bar", "lia" to "newlia"))
            }.message)

        assertEquals("Can only convert from String, but found \"15\" of type Int. Please provide a custom converter using @ConvertibleWith().",
            assertThrows<DynamicConversionException> {
                NestedConfig.constructFrom(mapOf("name" to 15, "lia" to cc.lia))
            }.message)
    }
}
