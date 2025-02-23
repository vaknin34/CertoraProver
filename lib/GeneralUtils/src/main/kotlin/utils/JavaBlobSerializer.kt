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

import datastructures.stdcollections.*
import kotlin.io.*
import kotlinx.serialization.*
import kotlinx.serialization.builtins.*
import kotlinx.serialization.descriptors.*
import kotlinx.serialization.encoding.*
import utils.*
import java.io.*
import java.io.Serializable
import java.math.BigInteger
import java.nio.file.*
import java.util.Base64

/**
    Kotlin serializer that defers to Java serialization.  Writes objects as Base64 encodings of java-serialized bytes.
    Use only when it's ok if a human cannot read/modify the serialized form, and normal Kotlin serialization will not
    work (for example, Kotlin serialization cannot handle inner classes, cycles in data structures, etc.).

    To use this, declare a derived class like so:

        class FooSerializer : JavaBlobSerializer<Foo>()

    ...and then use it in KSerializable annotations:

        @KSerializable
        data class Thing(@KSerializable(with = FooSerializer::class) val foo: Foo)

    ...or just put it on the class:

        @KSerializable(with = Foo.Serializer::class)
        class Foo : java.io.Serializable {
            class Serializer : JavaBlobSerializer<Foo>()
        }

    `MetaMap` uses this serializer automatically, for types with no Kotlin serializer of their own.
 */
open class JavaBlobSerializer<T : Serializable> : KSerializer<T> {
    companion object {
        val dumpFilePath by lazy {
            val timestamp = System.currentTimeMillis()
            val pid = ProcessHandle.current().pid()
            Path.of("JavaBlobSerializer.$timestamp.$pid.dump")
        }
    }

    override val descriptor: SerialDescriptor = String.serializer().descriptor

    override fun serialize(encoder: Encoder, value: T) {
        String.serializer().serialize(
            encoder,
            base64Serialize(value).also {
                /*
                    Some useful code for debugging serialization consistency issues
                 */

                /*
                   Dump all objects to a file for inspection:
                 */
                // debugJavaSerializationDump(base64Deserialize(it), dumpFilePath, append = true)

                /*
                   Validate round-trip encoding consistency:
                 */
                // val roundTripped = base64Serialize(base64Deserialize(it))
                // if (roundTripped != it) {
                //     File("JavaBlobSerializer.encoded.bin").writeBytes(Base64.getDecoder().decode(it))
                //     File("JavaBlobSerializer.encoded2.bin").writeBytes(Base64.getDecoder().decode(roundTripped))
                //     throw IllegalStateException(
                //         "JavaBlobSerializer: round-trip encoding mismatch.  " +
                //         "See JavaBlobSerializer.encoded.bin and JavaBlobSerializer.encoded2.bin.")
                // }
            }
        )
    }

    /**
        Because [JavaBlobSerializer]'s output is used for digest generation, we need to ensure that the output is
        consistent from run to run.  This is a problem sometimes, because the first run will be computing the serialized
        objects directly, while subsequent runs may be using objects deserialized from the cache.  Minor internal
        differences in the computed vs. deserialized objects can cause the serialized output to differ, breaking digest
        comparisons.

        Here are the known ways this can happen; we will likely find more over time:

        1. The JVM [HashMap]/[LinkedHashMap] classes serialize some internal details like the bucket count, expansion
           threshold, etc.  These can have different values depending on the details of how the maps were built up.
           These are not semantically important, but they affect the serialization byte stream.  We work around this by
           we-writing the maps to new instances with consistent values for these fields.

        2. BigInteger objects are not interned by the JVM.  Sometimes we may end up with a single shared object of a
           given value, while other times we might have two instances in the object graph.  This results in wildly
           different serialization.  We work around this by interning BigInteger here.

        3. BigInteger serializes some internal cached state, which depends on which BigInteger features have been used
           prior to serialization.  As with HashMap, we erase this state by creating fresh objects.

        4. Strings and boxed primitive types might be interned by the JVM, or they might not.  This can cause
           serialization differences.  We work around this by interning them here.
     */
    class CanonicalizingObjectOutputStream(out: OutputStream) : ObjectOutputStream(out) {
        init {
            enableReplaceObject(true)
        }

        private val internTable = mutableMapOf<Any, Any>()

        override fun replaceObject(obj: Any): Any = when (obj) {
            is String, is Byte, is Short, is Int, is Long, is Float, is Double, is Char, is Boolean -> internTable.getOrPut(obj) { obj }
            is HashMap<*, *> -> HashMap<Any?, Any?>(obj)
            is LinkedHashMap<*, *> -> LinkedHashMap<Any?, Any?>(obj)
            is HashSet<*> -> HashSet<Any?>(obj)
            is LinkedHashSet<*> -> LinkedHashSet<Any?>(obj)
            is BigInteger -> internTable.getOrPut(obj) { BigInteger(obj.toString()) }
            else -> obj
        }
    }

    override fun deserialize(decoder: Decoder): T =
        base64Deserialize(String.serializer().deserialize(decoder))

    fun javaSerialize(value: T) = ByteArrayOutputStream().use { bos ->
        CanonicalizingObjectOutputStream(bos).use { oos ->
            oos.writeObject(value)
        }
        bos.toByteArray()
    }

    fun javaDeserialize(bytes: ByteArray): T = ByteArrayInputStream(bytes).use { bis ->
        ObjectInputStream(bis).use { ois ->
            ois.readObject().uncheckedAs()
        }
    }

    fun base64Serialize(value: T): String = Base64.getEncoder().encodeToString(
        javaSerialize(value)
    )

    fun base64Deserialize(string: String): T = javaDeserialize(Base64.getDecoder().decode(string))
}
