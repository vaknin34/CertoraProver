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

package config

import annotations.PollutesGlobalState
import datastructures.stdcollections.*
import java.io.Closeable
import java.io.Serializable
import kotlin.reflect.KMutableProperty0

/**
 * Stores a list of config changes.
 *
 * Upon a call to [use], this will
 *   - snapshot the current config settings at time of the call to [use],
 *   - apply the settings saved in this [ConfigScope],
 *   - execute the given code block (argument to [use],)
 *   - revert to the settings from the snapshot before exiting (no matter how the exit is happening, regular,
 *   via exception, etc.).
 *
 * This is reusable and nestable. Updates (via [extend]) happen as "functional", non-destructive updates.
 *
 *  @param changes the changes to be made to config inside the `use` scope, and undone when that scope is exited
 */
class ConfigScope private constructor(private val changes: List<ConfigChange> = listOf()) {

    /** Note that [getUndo] must always be called before [apply] is called. */
    private sealed interface ConfigChange {
        /** takes a snapshot of the current setting for the given config option, and returns an action that sets the
         * config to that setting. */
        fun getUndo(): () -> Unit
        /** Applies the intended change to the current config. */
        fun apply()

        @OptIn(PollutesGlobalState::class)
        class Ct<T : Serializable>(val configType: ConfigType<T>, val newValue: T) : ConfigChange {
            override fun getUndo(): () -> Unit {
                return if (configType.isDefault()) {
                    { configType.reset() }
                } else {
                    val current = configType.get() ;
                    { configType.set(current) }
                }
            }

            override fun apply() {
                configType.set(newValue)
            }
        }

        class Prp<T>(val kProperty: KMutableProperty0<T>, val newValue: T) : ConfigChange {
            override fun getUndo(): () -> Unit {
                val current = kProperty.get();
                return { kProperty.set(current) }
            }

            override fun apply() {
                kProperty.set(newValue)
            }
        }
    }

    /** Lambdas that undo the changes made at the beginning of a `use`. This gets set by the [use] function and consumed
     * in the [close] function. */
    internal class Undoer(val undo: List<() -> Unit>) : Closeable {
        override fun close() {
            undo.asReversed().forEach { it() }
        }
    }

    /** Return a scope that is like this one, but with the given config setting added. */
    fun <T : Serializable> extend(config: ConfigType<T>, value: T): ConfigScope =
        ConfigScope(changes + ConfigChange.Ct(config, value))

    /** Return a scope that is like this one, but with the given config setting added. */
    fun <T> extend(property: KMutableProperty0<T>, value: T): ConfigScope =
        ConfigScope(changes + ConfigChange.Prp(property, value))


    /** Return a scope that incorporates the config settings of [this] and [other]. */
    infix operator fun plus(other: ConfigScope): ConfigScope =
        ConfigScope(this.changes + other.changes)


    /**
     * Executes these steps:
     *  - snapshot the current config settings,
     *  - apply the settings saved in this [ConfigScope]
     *  - execute [block]
     *  - revert to the settings from the snapshot before exiting (no matter how the exit is happening, regular,
     *    via exception, etc.)
     */
    inline fun <R> use(block: (ConfigScope) -> R): R = startUse().use { block(this) }

    @PublishedApi internal fun startUse(): Undoer {
        val undoer = Undoer(changes.map { it.getUndo() })
        changes.forEach { it.apply() }
        return undoer
    }

    companion object {
        /** Creates an "empty" scope object with no changes to the settings. */
        operator fun invoke() = ConfigScope()

        /** Creates the scope object and calls [ConfigScope.invoke] to set the configuration option. */
        operator fun <T : Serializable> invoke(config: ConfigType<T>, value: T) =
            ConfigScope(listOf(ConfigChange.Ct(config, value)))

        /** Creates the scope object and calls [ConfigScope.invoke] to set the property. */
        operator fun <T> invoke(property: KMutableProperty0<T>, value: T) =
            ConfigScope(listOf(ConfigChange.Prp(property, value)))
    }
}
