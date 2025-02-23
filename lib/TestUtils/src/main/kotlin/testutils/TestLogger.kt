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

/**
    A logger that logs to stdout.  Logging level is configured via JUnit [configuration
    parameters](https://junit.org/junit5/docs/current/user-guide/#running-tests-config-params).  For example, set
    `test.log.level.points.to=trace` to enable trace logging for the `POINTS_TO` logger.

    When running tests via Gradle, you can set these via gradle properties.  For example:
    ```
        ./gradlew test -Plevel.points.to=trace
    ```
 */
class TestLogger(val type: LoggerName) : Logger() {
    override val isEnabled get() = true
    override val isErrorEnabled get() = isEnabled(LoggerLevels.ERROR)
    override val isWarnEnabled get() = isEnabled(LoggerLevels.WARN)
    override val isInfoEnabled get() = isEnabled(LoggerLevels.INFO)
    override val isDebugEnabled get() = isEnabled(LoggerLevels.DEBUG)
    override val isTraceEnabled get() = isEnabled(LoggerLevels.TRACE)

    override fun error(t: Throwable?, msg: () -> Any) = log(LoggerLevels.ERROR, t, msg)
    override fun warn(t: Throwable?, msg: () -> Any) = log(LoggerLevels.WARN, t, msg)
    override fun info(t: Throwable?, msg: () -> Any) = log(LoggerLevels.INFO, t, msg)
    override fun debug(t: Throwable?, msg: () -> Any) = log(LoggerLevels.DEBUG, t, msg)
    override fun trace(msg: () -> Any) = log(LoggerLevels.TRACE, null, msg)

    private fun getVerbosityLevel(): LoggerLevels {
        System.getProperty("level.$type")?.let {
            return LoggerLevels.valueOf(it.uppercase())
        }
        System.getProperty("org.slf4j.simpleLogger.log.$type")?.let {
            return LoggerLevels.valueOf(it.uppercase())
        }
        return LoggerLevels.WARN
    }

    private val verbosityLevel: LoggerLevels = getVerbosityLevel()

    // The static logging functions (`alwaysError`, etc.) always log to stdout, so we don't want to duplicate those logs.
    private val isAlwaysLogger = type.name == "ALWAYS"

    private fun isEnabled(level: LoggerLevels) = !isAlwaysLogger && level.ordinal <= verbosityLevel.ordinal

    private fun log(level: LoggerLevels, t: Throwable?, msg: () -> Any) {
        if (isEnabled(level)) {
            System.out.println("${level.name} ${type.name} - ${msg()}")
            t?.printStackTrace(System.out)
        }
    }
}
