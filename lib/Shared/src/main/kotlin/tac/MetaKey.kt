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

import com.certora.collect.*
import config.Config
import datastructures.stdcollections.*
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.KSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.encoding.*
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.JsonDecoder
import kotlinx.serialization.json.JsonElement
import kotlinx.serialization.serializer
import utils.*
import java.io.Serializable
import java.math.BigInteger

/**
 * A [MetaKey] represents a particular type of metadata that may be associated with a node in the TAC AST (e.g. a
 * command, expression, or symbol).  Each AST node has a [MetaMap] that holds the values associated with the keys.
 *
 * @param T the type of data associated with this key
 *
 * @see [vc.data.TACMeta] for a list of many (but not all) MetaKeys
 */
@KSerializable(with = MetaKey.Serializer::class)
@Treapable
class MetaKey<T : Serializable> private constructor(
    private val name: String,
    val typ: Class<out T>,
    private val erasureStrategy: ErasureStrategy
) : AmbiSerializable {
    val isCanonical: Boolean
        get() = erasureStrategy == ErasureStrategy.Canonical
    val restore: Boolean
        get() = erasureStrategy == ErasureStrategy.CallTrace
    /**
     * Is the metadata indexed by this key
     * * canonical for a [ICoreTACProgram]
     * * should be erased from it
     * * not-canonical but needed for counter-example call-trace
     **/
    private enum class ErasureStrategy {
        Canonical,
        Erased,
        CallTrace;
    }

    override fun toString() = name

    override fun hashCode() = hash { it + name + typ + erasureStrategy }

    override fun equals(other: Any?) = when {
        other === this -> true
        other !is MetaKey<*> -> false
        other.name != this.name -> false
        other.typ != this.typ -> false
        other.erasureStrategy != this.erasureStrategy -> false
        else -> true
    }

    companion object {
        /**
         * MetaKey constructors
         * @param [restore] should the corresponding meta-value be restored from a cached TAC
         * @param [erased] should the corresponding meta-values be erased (i.e. ignored) when converting a TAC to its canonical representation,
         * defaults to [restore] since there if a meta-values needs restoration, its is not canonical - i.e. should be erased
         **/
        inline operator fun <@Treapable reified T : Serializable> invoke(
                name: String,
                restore: Boolean = false,
                erased: Boolean = restore
            ) = unsafeCreate(name, T::class.javaObjectType, erased = erased, restore)

        /** Create a marker key.  Marker keys are either present or absent, but contain no additional data */
        fun Nothing(name: String) =
            unsafeCreate(name, MetaMap.nothing::class.javaObjectType, erased = false, restore = false).uncheckedAs<MetaKey<Nothing>>()

        // Thunk from public inline functions to the private constructor.  Don't use this anywhere else.
        @PublishedApi
        internal fun <T : Serializable> unsafeCreate(
            name: String,
            typ: Class<T>,
            erased: Boolean,
            restore: Boolean
        ) = MetaKey<T>(
            name, typ, when {
                !erased -> ErasureStrategy.Canonical
                restore -> ErasureStrategy.CallTrace
                else -> ErasureStrategy.Erased
            }
        )
    }

    @KSerializable
    @SerialName("MetaKey")
    private class SerializationSurrogate(val name: String, val type: String, val erasureStrategy: ErasureStrategy)

    object Serializer : KSerializer<MetaKey<*>> {
        override val descriptor: SerialDescriptor = SerializationSurrogate.serializer().descriptor

        override fun serialize(encoder: Encoder, value: MetaKey<*>) {
            val surrogate = SerializationSurrogate(value.name, value.typ.name, value.erasureStrategy)
            encoder.encodeSerializableValue(SerializationSurrogate.serializer(), surrogate)
        }

        @Suppress("HashCodeStability")
        override fun deserialize(decoder: Decoder): MetaKey<*> {
            val surrogate = decoder.decodeSerializableValue(SerializationSurrogate.serializer())
            return MetaKey<Serializable>(
                surrogate.name,
                Class.forName(surrogate.type).uncheckedAs(),
                surrogate.erasureStrategy
            )
        }
    }
}

private typealias MetaMapEntry<T> = Pair<MetaKey<T>, T>

/**
 * A [MetaMap] is a map from [MetaKey]s to values.  It is used to associate semantic metadata to a TAC AST node.
 * TAC transformations preserve the meta maps.
 *
 * [MetaMap]s have heterogeneous values; the [MetaKey] determines the type of the stored data.  Aside from the types,
 * the API for [MetaMap] mirrors that of [Map].
 *
 * @see [vc.data.TACMeta] for a list of many (but not all) MetaKeys
 */
@JvmInline
@KSerializable(with = MetaMap.Serializer::class)
@Treapable
value class MetaMap private constructor(
    @Suppress("HashCodeStability") // We enforce hash code stability through MetaKey
    val map: TreapMap<MetaKey<*>, Serializable>
) : Serializable {

    constructor() : this(treapMapOf())

    constructor(key: MetaKey<Nothing>) : this(treapMapOf(key to nothing))

    operator fun plus(other: MetaMap) = MetaMap(this.map + other.map)
    operator fun <T : Serializable> plus(entry: MetaMapEntry<T>) = MetaMap(map + entry)
    operator fun plus(key: MetaKey<Nothing>): MetaMap = this + MetaMap(map + (key to nothing))
    operator fun <T : Serializable> minus(key: MetaKey<T>) = MetaMap(map - key)

    /** The number of entries in the map */
    val size : Int get() = map.size
    fun isEmpty() : Boolean = map.isEmpty()
    operator fun <T : Serializable> get(key: MetaKey<T>): T? = map[key]?.uncheckedAs()

    fun <T : Serializable> containsKey(key: MetaKey<T>) = map.containsKey(key)
    operator fun <T : Serializable> contains(key: MetaKey<T>) = containsKey(key)

    fun updateValues(transform: (MetaMapEntry<Serializable>) -> Serializable) =
        unsafeCreate(this.map.updateValues { k, v ->
            transform(k.uncheckedAs<MetaKey<Serializable>>() to v).also { newV ->
                // Validate the value.
                // We can short-circuit the expensive type check if we didn't change the value.
                check(newV === v || k.typ.isInstance(newV)) {
                    "MetaMap value $k:$v transformed to incompatible value $newV"
                }
            }
        })

    inline fun map(transform: (Map.Entry<MetaKey<*>, Serializable>) -> Pair<MetaKey<*>, Serializable>) =
        treapMapBuilderOf<MetaKey<*>, Serializable>().let {
            it.putAll(map.map { entry ->
                val (k, v) = transform(entry)
                check(k.typ.isInstance(v)) { "MetaMap value $v transformed to incompatible to key $k" }
                k to v
            })
            unsafeCreate(it.build())
        }

    inline fun filter(test: (Map.Entry<MetaKey<*>, Serializable>) -> Boolean) =
        treapMapBuilderOf<MetaKey<*>, Serializable>().let {
            it.putAll(map.filter(test))
            unsafeCreate(it.build())
        }

    companion object {
        operator fun <T : Serializable> invoke(entry: MetaMapEntry<T>) =
            MetaMap(treapMapOf(entry.uncheckedAs()))

        // Give inline functions access to our private constructor.  This should not be used outside of this class.
        @PublishedApi internal fun unsafeCreate(map: TreapMap<MetaKey<*>, Serializable>) = MetaMap(map)

        // Dummy value to associate with MetaKey<Nothing>.  Don't use this directly.  In particular, never
        // create a MetaKey<NothingValue>; use MetaKey.Nothing instead!
        @KSerializable
        @Treapable
        @Deprecated("Use MetaKey.Nothing instead") // this has to be public for serialization to work
        object NothingValue : AmbiSerializable {
            override fun hashCode() = hashObject(this)
            @Suppress("deprecation")
            private fun readResolve(): Any = NothingValue

            override fun toString(): String = "NoValue"
        }

        @Suppress("deprecation") // it's ok to expose the value, just not the type.
        val nothing: Serializable = NothingValue
    }

    @OptIn(ExperimentalSerializationApi::class)
    object Serializer : KSerializer<MetaMap> {
        private val listSerializer = ListSerializer(EntrySerializationSurrogate.serializer())
        override val descriptor: SerialDescriptor = SerialDescriptor("MetaMap", listSerializer.descriptor)

        override fun serialize(encoder: Encoder, value: MetaMap) {
            val list = value.map.map { (k, v) -> EntrySerializationSurrogate(k, v) }
            encoder.encodeSerializableValue(listSerializer, list)
        }
        override fun deserialize(decoder: Decoder): MetaMap {
            val list = decoder.decodeSerializableValue(listSerializer)
            return list.fold(MetaMap()) { acc, (k, v) ->
                MetaMap(acc.map + (k to v))
            }
        }
    }

    @KSerializable(with = EntrySerializationSurrogate.Serializer::class)
    data class EntrySerializationSurrogate(val key: MetaKey<*>, val value: Serializable) {
        @OptIn(ExperimentalSerializationApi::class)
        object Serializer : KSerializer<EntrySerializationSurrogate> {
            override val descriptor: SerialDescriptor =
                buildClassSerialDescriptor("Entry") {
                    element("key", MetaKey.Serializer.descriptor)
                    element("value", serializer(HasKSerializable::class.java).descriptor)
                }

            /**
             * Gets the serializer for the given class, or defers to [JavaBlobSerializer] for types that aren't
             * kotlin-serializable.
             */
            private fun <T : Serializable> serializer(typ: Class<T>): KSerializer<T> = when {
                typ == BigInteger::class.java -> BigIntegerSerializer().uncheckedAs()
                else -> kotlinx.serialization.serializerOrNull(typ).uncheckedAs()?: if (Config.AssertNoJavaBlobSerializer.get()) {
                    throw IllegalStateException("Attempted to use JavaBlobSerializer")
                } else {
                    JavaBlobSerializer()
                }
            }

            override fun serialize(encoder: Encoder, value: EntrySerializationSurrogate) {
                encoder.encodeStructure(descriptor) {
                    encodeSerializableElement(
                        descriptor, 0, MetaKey.Serializer, value.key
                    )
                    encodeSerializableElement<Serializable>(
                        descriptor, 1, serializer(value.key.typ).uncheckedAs(), value.value
                    )
                }
            }

            override fun deserialize(decoder: Decoder): EntrySerializationSurrogate {
                var key: MetaKey<*>? = null
                var value: Serializable? = null
                decoder.decodeStructure(descriptor) {
                    var valueElement : JsonElement? = null
                    while (true) {
                        when (val index = decodeElementIndex(descriptor)) {
                            0 -> {
                                key = decodeSerializableElement<MetaKey<*>>(descriptor, index, MetaKey.Serializer)
                                if(valueElement != null) {
                                    value = Json.decodeFromJsonElement(serializer(key!!.typ), valueElement)
                                }
                            }
                            1 -> {
                                /**
                                 Is this safe to do? It's very unclear from the public documentation. On the one hand the
                                 [JsonDecoder.decodeJsonElement] *very* loudly suggests it is not safe to call this function
                                 mid-serialization. But a reading of the JSON serialization internals suggests that decoding
                                 a json object mid-stream is perfectly fine, see
                                 [kotlinx.serialization.json.internal.StreamingJsonDecoder.decodeSerializableValue]. Looking
                                 at the implementation of [CompositeDecoder.decodeElementIndex] we can see that the internal
                                 pointer of the lexer points immediately to the value in the KV mapping, in other words,
                                 ... "value": { ..
                                             ^ here
                                 at which point decoding the element and then trying to deserialize later is fine.

                                 Yes this relies on undocumented internal API behavior, but the alternative is to make our
                                 serialization sensitive to order of map keys :-\
                                 */
                                if(key == null) {
                                    valueElement = (this as JsonDecoder).decodeJsonElement()
                                } else {
                                    val k = key!!
                                    value = decodeSerializableElement(descriptor, index, serializer(k.typ))
                                }
                            }
                            CompositeDecoder.DECODE_DONE -> break
                            else -> error("Unexpected index $index")
                        }
                    }
                }
                return EntrySerializationSurrogate(key!!, value!!)
            }
        }
    }
}
