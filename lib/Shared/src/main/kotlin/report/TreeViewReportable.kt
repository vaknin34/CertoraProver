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

package report

import config.Config.PrettyTreeViewReports
import kotlinx.serialization.json.*
import utils.*

/**
 * An object that may be shown in a treeView report.
 * The treeView representation of this object is a JSON element ([JsonElement]).
 * [toTreeViewRep] builds this representation using the [treeViewRepBuilder] attribute.
 */
interface TreeViewReportable {
    companion object {
        private val jsonFormatter = Json { prettyPrint = PrettyTreeViewReports.get() }
    }

    /**
     * Returns a JSON string serialization of the [JsonElement] returned by
     * [toTreeViewRep].
     * The string returned is pretty-printed if [PrettyTreeViewReports] config is set to true.
     */
    fun toJsonString(): String = jsonFormatter.encodeToString(JsonElement.serializer(), toTreeViewRep())

    /**
     * Gives the building steps of the JSON representation of this [TreeViewReportable] in the treeView.
     */
    val treeViewRepBuilder: TreeViewRepBuilder<*>

    /**
     * Returns the [JsonElement] that encodes the JSON representation of this [TreeViewReportable].
     */
    fun toTreeViewRep(): JsonElement = treeViewRepBuilder.build()

}

/**
 * A builder of the JSON element ([JsonElement]) that represents a [TreeViewReportable] instance.
 * @property builderAction Builder of the JSON element that uses a receiver of type [B].
 *
 */
interface TreeViewRepBuilder<B> {
    val builderAction: B.() -> Unit
    infix fun coalesceInto(builder: B) {
        builderAction(builder)
    }
    /**
     * Returns the [JsonElement] built using [builderAction].
     */
    fun build(): JsonElement
}

infix fun <B> (B.() -> Unit).coalesceInto(builder: B) = this(builder)

/**
 * An abstract, Kotlin serializable implementation of [TreeViewRepBuilder].
 */
private abstract class TreeViewRepSimpleBuilder<B> : TreeViewRepBuilder<B>

/**
 * A Kotlin serializable implementation of [TreeViewRepBuilder] that
 * lazily builds the [JsonElement] using the [builderAction].
 * This is achieved by caching the [JsonElement] returned by [doBuild],
 * and returning it in subsequent calls to [build].
 */
private abstract class TreeViewRepCachingBuilder<B> : TreeViewRepBuilder<B> {

    protected val cachedBuild: JsonElement by lazy(::doBuild)

    protected abstract fun doBuild(): JsonElement

    override fun build(): JsonElement = cachedBuild

}

/**
 * A builder of a JSON object ([JsonObject]) that represents a [TreeViewReportable] instance.
 */
object TreeViewRepJsonObjectBuilder {
    /**
     * @param caching whether to lazily build the [JsonElement] using [objectBuilderAction].
     * @param objectBuilderAction uses the DSL builder for [JsonObject]s ([JsonObjectBuilder]).
     */
    operator fun invoke(
        caching: Boolean = false,
        objectBuilderAction: JsonObjectBuilder.() -> Unit
    ): TreeViewRepBuilder<JsonObjectBuilder> =
        if (caching) {
            object : TreeViewRepCachingBuilder<JsonObjectBuilder>() {
                override val builderAction: JsonObjectBuilder.() -> Unit
                    get() = objectBuilderAction

                override fun doBuild(): JsonObject = buildJsonObject(builderAction)
            }
        } else {
            object : TreeViewRepSimpleBuilder<JsonObjectBuilder>() {
                override val builderAction: JsonObjectBuilder.() -> Unit
                    get() = objectBuilderAction

                override fun build(): JsonObject = buildJsonObject(builderAction)
            }
        }
}

/**
 * A builder of a JSON array ([JsonArray]) that represents a [TreeViewReportable] instance.
 */
object TreeViewRepJsonArrayBuilder {
    /**
     * @param caching whether to lazily build the [JsonElement] using [arrayBuilderAction].
     * @param arrayBuilderAction uses the DSL builder for [JsonArray]s ([JsonArrayBuilder]).
     */
    operator fun invoke(
        caching: Boolean = false,
        arrayBuilderAction: JsonArrayBuilder.() -> Unit
    ): TreeViewRepBuilder<JsonArrayBuilder> =
        if (caching) {
            object : TreeViewRepCachingBuilder<JsonArrayBuilder>() {
                override val builderAction: JsonArrayBuilder.() -> Unit
                    get() = arrayBuilderAction

                override fun doBuild(): JsonArray = buildJsonArray(builderAction)
            }
        } else {
            object : TreeViewRepSimpleBuilder<JsonArrayBuilder>() {
                override val builderAction: JsonArrayBuilder.() -> Unit
                    get() = arrayBuilderAction

                override fun build(): JsonArray = buildJsonArray(builderAction)
            }
        }
}
fun JsonArrayBuilder.add(element: TreeViewReportable): Boolean = add(element.toTreeViewRep())
fun JsonArrayBuilder.addAll(elements: Collection<TreeViewReportable>) = elements.forEach(::add)
fun JsonObjectBuilder.put(key: String, value: TreeViewReportable?): JsonElement? =
    put(key, value?.toTreeViewRep() ?: JsonNull)

fun <T> JsonObjectBuilder.putJsonArray(
    key: String,
    elements: Collection<T>,
    treeViewRepSelector: (T) -> TreeViewReportable
): JsonElement? = putJsonArray(key) { elements.forEach { add(treeViewRepSelector(it)) } }

fun JsonObjectBuilder.putJsonArray(
    key: String,
    elements: Collection<TreeViewReportable>
): JsonElement? = putJsonArray(key, elements) { it }


