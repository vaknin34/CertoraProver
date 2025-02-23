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

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions.*
import kotlinx.serialization.*
import kotlinx.serialization.modules.*
import kotlinx.serialization.json.Json

// Declare some classes at package scope....
interface I : HasKSerializable
@KSerializable data class A(val i1: Int) : I
@KSerializable data class AA(val i5: Int) : ReflectivePolymorphicSerializerTest.AbstractBase()

@OptIn(ExperimentalSerializationApi::class)
class ReflectivePolymorphicSerializerTest {

    // ...and some classes in a nested scope
    @KSerializable abstract class AbstractBase : I
    @KSerializable data class AB(val i6: Int) : AbstractBase()
    @KSerializable data class B(val i3: Int) : I

    val json = Json {
        serializersModule = serializersmodules.GeneralUtils
        allowStructuredMapKeys = true
        prettyPrint = true
    }

    @Test
    fun interfaze() {
        val value = listOf<I>(
            A(1),
            B(2),
            AA(3),
            AB(4),
        )

        val jsonText = json.encodeToString(value)
        val deserialized: List<I> = json.decodeFromString(jsonText)

        assertEquals(value, deserialized, "JSON text was: $jsonText")
    }

    @Test
    fun abstractClass() {
        val value = listOf<AbstractBase>(
            AA(3),
            AB(4),
        )

        val jsonText = json.encodeToString(value)
        val deserialized: List<I> = json.decodeFromString(jsonText)

        assertEquals(value, deserialized, "JSON text was: $jsonText")
    }
}

