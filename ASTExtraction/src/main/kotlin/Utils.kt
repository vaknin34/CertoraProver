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

@file:Suppress("MissingPackageDeclaration") // `main` is in default package

import kotlinx.serialization.json.Json
import utils.CVLSerializerModules

internal const val EXIT_SUCCESS = 0
internal const val EXIT_FAILURE = 1
internal const val EXIT_SYNTAX_FAILURE = 2

/** this is here to silence Detekt. we actually do want to use println in this module. */
@Suppress("ForbiddenMethodCall")
internal fun println(message: Any?) = kotlin.io.println(message)

internal fun errprintln(message: Any?) = System.err.println(message)

/** reads input from stdin until EOF and returns the input unchanged */
internal fun readUntilEndOfInput(): String {
    val stdinLines = generateSequence(::readLine)

    /** the separator restores the EOL that gets consumed by [readLine] */
    return stdinLines.joinToString(separator = "\n")
}

internal val lspJsonConfig = Json {
    serializersModule = CVLSerializerModules.modules
    encodeDefaults = true
}
