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

package testutils

import log.*
import org.slf4j.LoggerFactoryFriend


interface LogConfigScope {
    fun setLogLevel(type: LoggerName, lvl: LoggerLevels)
}

/**
Establishes a scope for dynamic log configuration.  Note that this only applies to loggers that are created
inside of the scope; pre-existing loggers are already configured.

This is fundamentally not thread-safe.  Thankfully, tests do not run in parallel in a single process.
 */
fun <T> logConfigScope(f: context(LogConfigScope)() -> T) {

    val toUndo = mutableListOf<() -> Unit>()

    val scope = object : LogConfigScope {
        override fun setLogLevel(type: LoggerName, lvl: LoggerLevels) {
            val levelProp = "org.slf4j.simpleLogger.log.${type}"
            val topicProp = "topic.${type}"

            val oldlvl: String? = System.getProperty(levelProp)
            if (oldlvl == null) {
                toUndo += { System.clearProperty(levelProp) }
            } else {
                toUndo += { System.setProperty(levelProp, oldlvl) }
            }

            System.setProperty(levelProp, lvl.toString())

            if (System.getProperty(topicProp) == null) {
                toUndo += { System.clearProperty(topicProp) }
                System.setProperty(topicProp, "1")
            }
        }
    }

    LoggerFactoryFriend.reset()
    try {
        f(scope)
    } finally {
        toUndo.forEach { it() }
        LoggerFactoryFriend.reset()
    }
}
