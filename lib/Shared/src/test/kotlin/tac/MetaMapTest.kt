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

package tac


import compiler.SourceContext
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions.*
import java.io.ByteArrayInputStream
import java.io.ObjectInputStream
import java.io.ObjectOutputStream
import java.io.ByteArrayOutputStream
import java.io.Serializable
import kotlinx.serialization.decodeFromString
import kotlinx.serialization.encodeToString
import kotlinx.serialization.json.Json
import utils.*
import java.math.BigInteger

@KSerializable
class MyCustomValueType<T> : AmbiSerializable

data class NotKSerializable(val x: Int) : java.io.Serializable

@OptIn(kotlinx.serialization.ExperimentalSerializationApi::class)
class MetaMapTest {

    @Test
    fun metaKeyKotlinSerialization() {

        val key = MetaKey<MyCustomValueType<Int>>("my.custom.type")

        // Check that we can serialize the key to JSON, and deserialize an equivalent key.
        // We can't use the concrete type of the key as the generic type argument to encodeToString or decodeToString,
        // because the Kotlin serialization library throws an exception saying it can't find a serializer for that
        // particular concrete type.  That's fine, since in practice we won't be deserializing these with a
        // known-a-priori type; the type comes from the jsonSerialized form itself.

        val json = Json.encodeToString(key.uncheckedAs<MetaKey<Serializable>>())

        val jsonDeserialized = Json.decodeFromString<MetaKey<Serializable>>(json)

        assertEquals(key, jsonDeserialized)
    }


    @Test
    fun metaMapSerialization() {
        val bool = MetaKey<Boolean>("bool")
        val int = MetaKey<Int>("int")
        val string = MetaKey<String>("string")
        val bigInteger = MetaKey<BigInteger>("bigInteger")
        val nothing = MetaKey.Nothing("nothing")
        val sym = MetaKey<evm.SighashInt>("sighash")
        val ns = MetaKey<NotKSerializable>("ns")

        val map = MetaMap()
            .plus(bool to false)
            .plus(int to 42)
            .plus(string to "hello")
            .plus(bigInteger to BigInteger.TWO)
            .plus(nothing)
            .plus(sym to evm.SighashInt(12345.toBigInteger()))
            .plus(ns to NotKSerializable(12))

        // Round-trip JSON serialization
        val json = Json {
            allowStructuredMapKeys = true
        }
        val jsonSerialized = json.encodeToString(MetaMap.Serializer, map)
        val jsonDeserialized = json.decodeFromString(MetaMap.Serializer, jsonSerialized)
        assertEquals(map, jsonDeserialized)

        // Round-trip Java serialization
        val bos = ByteArrayOutputStream()
        val oos = ObjectOutputStream(bos)
        oos.writeObject(map)
        oos.flush()
        val javaSerialized = bos.toByteArray()
        val bis = ByteArrayInputStream(javaSerialized)
        val ois = ObjectInputStream(bis)
        val javaDeserialized = ois.readObject()
        assertEquals(map, javaDeserialized)
    }
}
