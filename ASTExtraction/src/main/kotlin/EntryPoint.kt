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

import kotlinx.serialization.encodeToString
import spec.CVLInput
import spec.CVLSource
import spec.DummyTypeResolver
import spec.cvlast.CVLAst
import spec.cvlast.SolidityContract
import spec.cvlast.typechecker.CVLError
import utils.CollectingResult
import java.io.File
import kotlin.system.exitProcess

/**
 * This entry point allows syntax checking of CVL spec files from the command line. Used by the LSP server.
 *
 * Input is in the form of a single file. If syntax checking passes, a [CVLAst] is emitted to stdout.
 * If it fails, [CVLError]s are emitted to stderr. Serialization is done via JSON.
 * Currently only basic syntax checking is done. For example, types are not validated and imports are not considered.
 *
 * Supported modes:
 *   ASTExtraction.jar -f FILE: takes a path to a single CVL file, emits a syntax check, then exits.
 *   ASTExtraction.jar -r: listens for input on stdin (in the form of an entire CVL file), emits a syntax check, then exits.
 */
fun main(args: Array<String>) {
    val source = when (args.getOrNull(0)) {
        "-f", "--file" -> {
            val path = args.getOrNull(1) ?: usage()
            val file = File(path).takeIf(File::isFile) ?: badFile(path)

            CVLSource.File(filepath = file.absolutePath, origpath = file.absolutePath, isImported = false)
        }

        "-r", "--raw" -> {
            val input = readUntilEndOfInput()

            CVLSource.Raw(name = "", rawTxt = input, isImported = false)
        }

        else -> usage()
    }

    CVLInput.Plain(source).emitAst()
}

private fun CVLInput.Plain.emitAst() {
    val primaryContract = SolidityContract(name = "")
    val typeResolver = DummyTypeResolver(primaryContract)

    when (val astOrErrors = getRawCVLAst(typeResolver)) {
        is CollectingResult.Result -> {
            val entireAst: CVLAst = astOrErrors.result
            val serialized = lspJsonConfig.encodeToString(entireAst)
            println(serialized)
            exitProcess(EXIT_SUCCESS)
        }

        is CollectingResult.Error -> {
            val errors: List<CVLError> = astOrErrors.messages
            val serialized = lspJsonConfig.encodeToString(errors)
            errprintln(serialized)
            exitProcess(EXIT_SYNTAX_FAILURE)
        }
    }
}

private fun usage(): Nothing {
    println("Usage:")
    println("  ASTExtraction.jar -f FILE | --file FILE")
    println("  ASTExtraction.jar -r | --raw")

    exitProcess(EXIT_FAILURE)
}

private fun badFile(path: String): Nothing {
    errprintln("invalid file: $path")

    exitProcess(EXIT_FAILURE)
}

