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

import datastructures.stdcollections.*
import ksp.dynamicconversion.DynamicConverter
import utils.uncheckedAs
import java.lang.Integer.min

/**
 * Custom exception for errors during configuration handling
 */
class ConfigurationException(msg: String) : Exception(msg)

/**
 * Little parser for custom JSON-like object notation meant for structured
 * command line arguments. Supports strings, lists, maps and named maps (a
 * string that usually represents some predefined object and a map that usually
 * contains modifications to that object).
 * The syntax is as follows:
 *  V := regex([a-zA-Z0-9:_-]+)
 *  List := [] | [ O (, O)* ]
 *  Map := {} | { V=O (, V=O)* }
 *  Obj := V | List | Map | V Map
 * The main method [parse] returns [Any], which is any of the following:
 * [String], [List<Any>], [Map<String,Any>], or [Pair<String,Map<String,Any>>]
 * and all nested [Any] types are again from these types.
 */
class CLIParser(val input: String) {
    var s: CharSequence = input.dropWhitespace()

    /**
     * Trim leading whitespace. As a convention, the current input [s] should
     * not have leading whitespaces at the beginning and when returning from
     * any parsing function.
     */
    private fun CharSequence.dropWhitespace() = trimStart()

    /** Check that the input continues with [e] and consume it. */
    private fun consume(e: String, msg: String) {
        if (!s.startsWith(e)) {
            val found = s.subSequence(0, min(s.length, e.length + 5))
            throw ConfigurationException("expected \"${e}\" but found \"${found}\": ${msg}")
        }
        s = s.drop(e.length).dropWhitespace()
    }

    /** Parse and return a quoted string literal, allow for both ' and " */
    private fun parseQuotedString(): String {
        val quote = s.first()
        check(quote in "'\"") { "string quotes should be ' or \"" }
        consume(quote.toString(), "Start of quoted string")
        val indexOfEndQuote = s.indexOfFirst { it == quote }
        if (indexOfEndQuote == -1) {
            throw ConfigurationException("unterminated quoted string")
        }
        val res = s.substring(0, indexOfEndQuote)
        // Here we know that s[id] == quote, no need to check it again via consume()
        s = s.drop(indexOfEndQuote + 1).dropWhitespace()
        return res
    }

    /** Parse and return a string value */
    private fun parseValue(): String {
        if (s.first() in "'\"") {
            return parseQuotedString()
        }
        var id = s.indexOfFirst { !(it.isLetterOrDigit() || it in ":_-") }
        if (id == -1) {
            id = s.length
        }
        val res = s.substring(0, id)
        s = s.drop(id).dropWhitespace()
        return res
    }

    /** Parse and return a list */
    private fun parseList(): List<Any> {
        consume("[", "Start of a list")
        val res = mutableListOf<Any>()
        while (s.isNotEmpty() && s.first() != ']') {
            res.add(parseInner())
            if (s.isEmpty() || s.first() == ']') break
            consume(",", "Separation of list entries")
        }
        consume("]", "End of a list")
        return res
    }

    /** Parse and return a map */
    private fun parseMap(): Map<String, Any> {
        consume("{", "Start of map")
        val res = mutableMapOf<String, Any>()
        while (s.first() != '}') {
            val k = parseValue()
            consume("=", "Map assignment")
            val v = parseInner()
            res[k] = v
            if (s.isEmpty() || s.first() == '}') break
            consume(",", "Separation of map entries")
        }
        consume("}", "End of map")
        return res
    }

    /** Parse and return any object */
    private fun parseInner(): Any {
        return when (s.first()) {
            '[' -> parseList()
            '{' -> parseMap()
            else -> {
                val v = parseValue()
                if (s.isNotEmpty() && s.first() == '{') {
                    Pair<String, Any>(v, parseMap())
                } else {
                    v
                }
            }
        }
    }

    /** Tries to return a good error message when parsing failed. */
    private fun errorMessage(): String = when {
        s.first() == ',' -> "Use \"[foo,bar]\" to specify a list of values."
        s.first() == '=' -> "Use \"{foo=bar}\" to specify a map or specialize an object."
        else -> ""
    }

    /** Parse and return any object, checks that the whole input was parsed. */
    fun parse(): Any {
        return try {
            val result = parseInner()
            if (s.isNotEmpty()) {
                throw ConfigurationException(errorMessage())
            }
            result
        } catch (e: ConfigurationException) {
            throw ConfigurationException(
                "Failed to parse argument \"${input}\" at \"${s}\". ${e.message}\nThis error may be caused by incorrect escaping on the command line."
            )
        }
    }
}

/**
 * Base class for something that is configurable. A set of configurable
 * objects is stored in a [Configuration.Registry] (which is usually used as the
 * base class for the companion object)). Such registries can also be nested to
 * group configurations. Let for example [SolverConfig] be such a configurable
 * class and assume nested registries for [SolverConfig] objects for cvc5 and
 * z3; we can obtain configurations in various ways:
 * - `SolverConfig.z3` to obtain the configuration registry for `z3`
 * - `SolverConfig.cvc5.nonlin` to obtain the configuration `nonlin` for `cvc5`
 * - `SolverConfig.z3.default.copy(bar=true)` to get the default preset for `z3`
 *   and set its member `bar` to `true`
 * Additionally, we can obtain configurations by string (either a single string
 * with components separated by `:` or an array of strings). Assuming that the
 * `z3` registry's default is `def`, the following all return the same
 * configuration:
 * - `SolverConfig.z3("def")`
 * - `SolverConfig.z3["def"]`
 * - `SolverConfig("z3:def")`
 * - `SolverConfig["z3", "def"]`
 *
 * If a [Configurable] should also be parsed from a string (e.g. from a
 * command line argument) it can be used together with [ConversionHelper] and
 * the [AddDynamicConversion] annotation.
 */
interface Configurable {
    /** The name of the configuration used for lookup by string */
    val configName: String
    /**
     * If set, the object is a placeholder for a list of configurables. This
     * should only be set if the object was obtained via [Configuration.resolve].
     */
    val configList: List<Configurable>?
    /**
     * Obtain a copy of this [Configurable] where [configList] is set to
     * [expands]. Should usually be a simple forward to [copy].
     */
    fun asConfigList(expands: List<Configurable>): Configurable

    /**
     * Simple utility to help with converting from the result of [CLIParser] to
     * some other class. The idea is that this helper is used in tandem with
     * the [AddDynamicConversion] annotation: a data class [T] is annotated
     * with this annotation and its companion object implements this interface.
     * [doCopy] and [doConstruct] should simply forward to `t.copy(override)`
     * and `constructFrom(params)`, respectively, and [construct] can then be
     * used to easily implement a [DynamicConverter] for [T].
     * When all of this is in place, we can use [parseOne] and [parseList] to
     * convert strings to instances of [T] or lists of [T], respectively.
     */
    interface ConversionHelper<CRT : Configurable> {
        /** Copy [t] and update it, usually `t.copy(override)` */
        fun doCopy(t: CRT, override: Map<String, Any>? = null): CRT

        /** Construct a [CRT] from the parameters, usually `constructFrom(params)` */
        fun doConstruct(params: Map<String, Any>): CRT

        /**
         * Construct a [CRT] from an object as parsed by [CLIParser]. Objects
         * may be retrieved from the given registry [reg].
         */
        fun construct(a: Any, reg: Configuration<CRT>): CRT {
            return when (a) {
                is String -> reg.resolve(a)
                is Pair<*, *> -> doCopy(reg.resolve(a.first.uncheckedAs()), a.second.uncheckedAs())
                is Map<*, *> -> doConstruct(a.uncheckedAs())
                else -> throw ConfigurationException("Can not convert ${a} to ${this::class.simpleName}")
            }
        }
    }
}

/**
 * Parse a single object of type [T], using [CLIParser] for parsing and [conv]
 * for the conversion.
 */
fun <T: Configurable> parseOne(input: String, conv: DynamicConverter<T>): T {
    return conv(CLIParser(input).parse()).also {
        if (it.configList != null) {
            throw ConfigurationException("Resulting object actually wraps a list: ${it}")
        }
    }
}

/**
 * Parse a list of objects of type [T], using [CLIParser] for parsing and
 * [conv] for the conversion. If the input is not a list but a single object,
 * a list of that single object is returned.
 */
fun <T: Configurable> parseList(input: String, conv: DynamicConverter<T>): List<T> {
    return when (val parsed = CLIParser(input).parse()) {
        is List<*> -> parsed.mapNotNull { it?.let { conv(it) } }
        else -> listOf(conv(parsed))
    }.flatMap { it.configList?.uncheckedAs() ?: listOf(it) }
}

/**
 * A registry for configurable objects. If used as a sub-registry, the [name]
 * is used as [Configurable.configName].
 */
sealed class Configuration<C : Configurable> {
    /**
     * Retrieve a single configuration by name from this registry. The name is
     * expected to be a proper path into this registry tree: if a sub-registry
     * is present for the given name, recurse to that sub-registry. The name is
     * given as `vararg` [names] for this purpose: the first name is used for
     * the main registry while the remaining strings are passed on to the
     * recursive call.
     */
    abstract operator fun get(vararg names: String): C

    /** Return all configurations in this or a sub-registry as a flat sequence. */
    abstract val values: List<C>
    /** Return the default configuration for this registry. */
    abstract val default: C

    /**
     * Retrieve a configuration by the given [name], which is split at `:` to
     * be used as path into this registry tree. The resulting configuration may
     * have [Configurable.configList] set: in this case, it represents a list
     * of configurations that should be expanded. [parseList] will do that for
     * you, or you can directly look at [Registry.values].
     */
    internal fun resolve(name: String? = null): C = get(*(name?.split(':')?.toTypedArray() ?: arrayOf()))

    /**
     * Retrieve a configuration by the given [name], which is split at `:` to
     * be used as path into this registry tree. If the result wraps a list,
     * i.e. [Configurable.configList] is set, a  [ConfigurationException] is
     * thrown.
     */
    operator fun invoke(name: String? = null): C = resolve(name).also {
        if (it.configList != null) {
            throw ConfigurationException("Resulting object actually wraps a list: ${it}")
        }
    }

    open class Registry<C : Configurable>(val name: String, val defaultName: String? = null) : Configuration<C>() {
        /** Actual registry lookup */
        private val registry = mutableMapOf<String, Configuration<C>>()

        /** Register a [Configurable] object in this registry. */
        fun register(e: C) = e.also {
            registry[e.configName] = Concrete(e)
        }

        /** Register a sub-registry in this registry. */
        fun <T : Registry<C>> register(e: T) = e.also {
            registry[e.name] = e
        }

        override operator fun get(vararg names: String): C {
            return if (names.isEmpty()) {
                default.asConfigList(values).uncheckedAs()
            } else {
                registry[names.first()]?.get(*(names.sliceArray(1 until names.size)))
                    ?: throw ConfigurationException("${names.first()} does not exist in this registry")
            }
        }

        override val values get() = registry.values.flatMap { it.values }
        override val default get() = registry[defaultName]?.get()
            ?: throw ConfigurationException("No name was given, and no default is specified.")
    }

    data class Concrete<C : Configurable>(override val default: C) : Configuration<C>() {
        override operator fun get(names: Array<out String>) = default.also {
            if (names.isNotEmpty()) {
                throw ConfigurationException("There is no sub-configuration ${names.joinToString(":")}, $it is already a configuration.")
            }
        }

        override val values get() = listOf(default)
    }
}
