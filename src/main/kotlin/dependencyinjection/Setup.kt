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

package dependencyinjection

import config.Config
import datastructures.stdcollections.*
import log.*
import utils.InjectedDependencies

fun validateLoggerNames() {
    // Find any logger names that are duplicated across our various components.
    val duplicates = (
        LoggerTypes.values().asSequence() +
        SMTLIBUtilsLoggerTypes.values().asSequence() +
        GeneralUtilsLoggerTypes.values().asSequence()
    ).groupBy { it.name }.entries.filter { it.value.size > 1 }

    check(duplicates.isEmpty()) {
        "Duplicate logger names:\n${duplicates.joinToString("\n") { "${it.key} -> ${it.value.joinToString { it::class.simpleName!! }}" }}"
    }
}

/**
 * Set up the [InjectedDependencies] object.
 */
fun setupDependencyInjection() {

    validateLoggerNames()

    InjectedDependencies.obj = object : InjectedDependencies {
        override fun getLogger(name: LoggerName) = KotlinLoggingLogger(name)

        override fun getFilePathForSmtQuery(name: String, subdir: String?) =
            ArtifactManagerFactory().getFilePathForSmtQuery(name, subdir)

        override fun registerArtifact(name: String, action: (String) -> Unit) =
            ArtifactManagerFactory().registerArtifact(name, action = action)

        override fun smt_dumpAll() = Config.Smt.DumpAll.get()

        override fun alwaysLogError(msg: String) = Logger.alwaysError(msg)
    }
}
