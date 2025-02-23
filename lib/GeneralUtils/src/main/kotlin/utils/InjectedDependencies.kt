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

import log.*
import smt.SmtDumpEnum

/**
 * Interface for dependency injection that offers access to infrastructure like
 * logging, artifacts, or configuration.
 */
interface InjectedDependencies {
    /** Register a logger with the given [type]. */
    fun getLogger(name: LoggerName): Logger = Logger.None
    /** Retrieve the file path for an SMT query artifact */
    fun getFilePathForSmtQuery(name: String, subdir: String? = null): String = name
    /** Register a new artifact and call [action] on the full filename */
    fun registerArtifact(name: String, action: ((String) -> Unit)): Unit = Unit
    /** Retrieve the config value for smt_dumpAllSessions */
    fun smt_dumpAll(): SmtDumpEnum = SmtDumpEnum.DISABLED

    /** Log an error unconditionally */
    fun alwaysLogError(msg: String) = Unit

    companion object {
        /** Holds the object that gives access to the dependencies */
        var obj: InjectedDependencies = object : InjectedDependencies {}

        /** Easy access to [obj], or throw if it was not set up properly */
        operator fun invoke(): InjectedDependencies = obj
    }
}
