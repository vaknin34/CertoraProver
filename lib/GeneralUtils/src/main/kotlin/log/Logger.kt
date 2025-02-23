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

package log

import utils.InjectedDependencies

/**
 * Our abstraction of a logger, ultimately forwarding to [KLogger]. It offers
 * the usual levels error, warn, info, debug, and trace. We generally offer two
 * methods for each level, taking a lazy log message (`() -> Any`), and a
 * `Throwable?` in addition to the lazy log message, respectively.
 * For error, we additionally offer overloads using a `String` message for
 * legacy reasons, for trace we don't take a throwable.
 * While error and warn are always forwarded to the underlying logger, info,
 * debug and trace are restricted by [isEnabled] returning true.
 * Customization should happen in the overloads taking a throwable and a lazy
 * log message (`t: Throwable?, msg: () -> Any`), all other overloads forward
 * to this one.
 */
abstract class Logger {
    abstract val isEnabled: Boolean
    abstract val isErrorEnabled: Boolean
    abstract val isWarnEnabled: Boolean
    abstract val isInfoEnabled: Boolean
    abstract val isDebugEnabled: Boolean
    abstract val isTraceEnabled: Boolean

    abstract fun error(t: Throwable?, msg: () -> Any)
    fun error(msg: () -> Any) = error(null, msg)
    fun error(msg: String) = error(null, msg)
    fun error(t: Throwable?, msg: String) = error(t) { msg }

    abstract fun warn(t: Throwable?, msg: () -> Any)
    fun warn(msg: () -> Any) = warn(null, msg)

    abstract fun info(t: Throwable?, msg: () -> Any)
    fun info(msg: () -> Any) = info(null, msg)

    abstract fun debug(t: Throwable?, msg: () -> Any)
    fun debug(msg: () -> Any) = debug(null, msg)

    abstract fun trace(msg: () -> Any)

    object None : Logger() {
        override val isEnabled get() = false
        override val isErrorEnabled get() = false
        override val isWarnEnabled get() = false
        override val isInfoEnabled get() = false
        override val isDebugEnabled get() = false
        override val isTraceEnabled get() = false
        override fun error(t: Throwable?, msg: () -> Any) = Unit
        override fun warn(t: Throwable?, msg: () -> Any) = Unit
        override fun info(t: Throwable?, msg: () -> Any) = Unit
        override fun debug(t: Throwable?, msg: () -> Any) = Unit
        override fun trace(msg: () -> Any) = Unit
    }

    companion object {
        /**
            Create an appropriate [Logger] instance for this environment, from the injected dependencies.
         */
        operator fun invoke(name: LoggerName) = InjectedDependencies().getLogger(name)
    }
}
