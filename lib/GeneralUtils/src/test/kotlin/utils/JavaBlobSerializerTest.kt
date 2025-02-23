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
import kotlinx.serialization.json.Json
import java.io.Serializable




@OptIn(ExperimentalSerializationApi::class)
class JavaBlobSerializerTest {

    data class A(val s: String, val i: Int) : Serializable

    @KSerializable(with = BSerializer::class)
    data class B(val a: A, val s: String) : Serializable

    @KSerializable
    data class C(val s: String, @KSerializable(with = ASerializer::class) val a: A) : Serializable

    class ASerializer : JavaBlobSerializer<A>()
    class BSerializer : JavaBlobSerializer<B>()

    inline fun <reified T : Serializable> roundTrip(value: T) {
        val jsonText = Json.encodeToString(value)
        val decoded: T = Json.decodeFromString(jsonText)
        assertEquals(value, decoded)
    }

    @Test
    fun annotOnClass() {
        roundTrip(B(A("hello", 12897), "there"))
    }

    @Test
    fun annotOnProp() {
        roundTrip(C("hi there", A("blah", 89897)))
    }
}

