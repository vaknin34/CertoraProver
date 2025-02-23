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

import kotlinx.serialization.KSerializer
import kotlinx.serialization.json.Json
import java.io.Externalizable
import java.io.ObjectInput
import java.io.ObjectOutput
import java.io.ObjectStreamException

/**
 * A proxy class for serializing kotlin serializable objects (i.e., with @Serializable) to a java serialization stream.
 *
 * Given a [serializer] for a type [T] and an instance of [toWrite], this class will serialize the JSON representation
 * (as produced by [serializer]) to an [ObjectOutput] stream. During deserialization, this reads the json representation
 * from the [ObjectInput] stream, and via the [readResolve] mechanism replaces itself with the result of deserializing the
 * JSON representation (again, using [serializer]).
 *
 * Implementers of this class *MUST* provide a no-arg constructor that passes a valid instance [serializer] to this
 * classes constructor.
 */
abstract class SerializationAdapter<T: Any>(private val serializer: KSerializer<T>, private var toWrite : T? = null) : Externalizable {
    private var data: String? = null

    protected open val json : Json get() = Json

    override fun readExternal(`in`: ObjectInput) {
        data = `in`.readObject() as String
    }

    override fun writeExternal(out: ObjectOutput) {
        data = json.encodeToString(serializer, toWrite!!)
        out.writeObject(data!!)
    }

    @Throws(ObjectStreamException::class)
    fun readResolve() : Any {
        return json.decodeFromString(serializer, data!!)
    }
}

/**
 * Mark an object as serializable with the Adapter mechanism used above.
 * This interface requires that implementing classes provide a [writeReplace]
 * method. This method should return an object that is serializable; in principle
 * any object will do, but it is expected that this method simply returns an instance
 * of a subclass of [SerializationAdapter].
 *
 * Example:
 * @Serializable
 * class Foo : SerializableWithAdapter {
 *    private class Adapter(x: Foo? = null) : SerializationAdapter(Foo.serializer(), x)
 *
 *    fun writeReplace() : Any = Adapter(this)
 *    ...
 * }
 *
 * The default value for x in the above is *crucial*: without no default constructor will be generated
 * and deserialization will fail.
 */
interface SerializableWithAdapter : AmbiSerializable {
    fun writeReplace() : Any
}
