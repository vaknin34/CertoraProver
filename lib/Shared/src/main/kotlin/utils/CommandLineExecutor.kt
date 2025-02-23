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

import log.ArtifactManagerFactory
import log.Logger
import log.LoggerTypes
import os.setCriticality
import java.io.File
import java.io.FileReader
import java.io.PrintWriter
import java.lang.Thread.sleep
import java.nio.charset.Charset
import java.util.concurrent.TimeUnit


private val logger = Logger(LoggerTypes.COMMON)

fun safeCommandArrayExecLines(
    cmd: Array<String>,
    outputName: String,
    readStandardOutput: Boolean = false,
    checkExitCode: Boolean = true,
    timeoutSecs: Long?,
    input: String? = null,
    critical: Boolean = true,
): Pair<Int, List<String>> {
    val redirectStdoutStderr = readStandardOutput && ArtifactManagerFactory.isEnabled() // suppress outputs
    val fileError = try {
        if (redirectStdoutStderr) File(ArtifactManagerFactory().getCmdErrorFilepath(outputName)) else null
    } catch (_: IllegalStateException) {
        null
    }
    val fileOutput = try {
        if (redirectStdoutStderr) File(ArtifactManagerFactory().getCmdOutputFilepath(outputName)) else null
    } catch (_: IllegalStateException) {
        null
    }
    val hasRedirects = fileError != null && fileOutput != null
    val stringCommand = cmd.joinToString(" ")
    check(!redirectStdoutStderr || hasRedirects) { "If asked to redirect from stdout/stderr, must have path for output file" }
    if (hasRedirects && redirectStdoutStderr) {
        PrintWriter(fileError!!).use { writer -> writer.println("stderr: $stringCommand") }
        PrintWriter(fileOutput!!).use { writer -> writer.println("stdout: $stringCommand") }
    }
    @Suppress("DEPRECATION")
    logger.debug { "Thread ${Thread.currentThread().id}: Going to start $stringCommand" }
    val p = ProcessBuilder()
        .command(*cmd)
        .let {
            if (redirectStdoutStderr) {
                it.redirectError(ProcessBuilder.Redirect.appendTo(fileError))
                    .redirectOutput(ProcessBuilder.Redirect.appendTo(fileOutput))
            } else {
                it
            }
        }
        .start()
        .apply { setCriticality(critical) }

    if (input != null) {
        p.outputStream.use { out ->
            out.write(input.toByteArray(Charset.defaultCharset()))
        }
    }
    sleep(100)

    val bufferedOutputReader = p.inputStream.reader().buffered()
    val exitValue: Int

    try {
        if (timeoutSecs != null) {
            p.waitFor(timeoutSecs, TimeUnit.SECONDS)
        } else {
            p.waitFor()
        }
    } catch (e: InterruptedException) {
        p.destroyForcibly()
    } finally {
        cleanUpProcess(p)
        exitValue = p.exitValue()
    }

    if (checkExitCode && exitValue != 0) {
        val errors = fileError?.path?.let { path -> FileReader(path).readText() } ?: "?"
        throw Exception("Failed to run command ($stringCommand), exited with code $exitValue, see errors: ${fileError?.path ?: "N/A"}, output: ${fileOutput?.path ?: "N/A"}. Details: $errors")
    }

    val lineList = if (redirectStdoutStderr) {
        FileReader(fileOutput!!).use { reader -> reader.readLines() }
    } else if (readStandardOutput) { // danger of blocking here
        bufferedOutputReader.readLines()
    } else {
        emptyList()
    }

    return Pair(exitValue, lineList)
}

private fun noInterrupt(f: () -> Unit) {
    var again: Boolean
    do {
        try {
            f()
            again = false
        } catch (e: InterruptedException) {
            again = true
            val loc = e.stackTrace[1]
            @Suppress("DEPRECATION")
            logger.warn { "Thread ${Thread.currentThread().id}: Got Interrupted exception during noInterrupt at ${loc.methodName} in ${loc.fileName}:${loc.lineNumber}" }
        }
    } while (again)
}


private fun catchInterrupt(f: () -> Unit) {
    try {
        f()
    } catch (e: InterruptedException) {
        val loc = e.stackTrace[1]
        @Suppress("DEPRECATION")
        logger.warn { "Thread ${Thread.currentThread().id}: Got Interrupted exception during catchInterrupt at ${loc.methodName} in ${loc.fileName}:${loc.lineNumber}" }
    }
}


class Killer(p: ProcessHandle) {

    val allChilds = mutableListOf<ProcessHandle>(p)

    init {
        getChilds(p)
    }

    private fun getChilds(p: ProcessHandle) {
        p.children().forEach {child ->
            allChilds.add(child)
            getChilds(child)
        }
    }

    fun destroyChilds() {
        allChilds.forEach { child ->
            child.destroy()
        }
    }

    fun destroyChildsForcibly() {
        allChilds.forEach { child ->
            if (child.isAlive) {
                child.destroyForcibly()
        }
    }
    }

    }

private fun cleanUpProcess(p: Process) {
    try {
        if (!p.isAlive) {
            /* Not sure this line does anything after !isAlive, but leaving it for now */
            @Suppress("DEPRECATION")
            logger.debug { "Thread ${Thread.currentThread().id}: Process ${p.pid()} was dead before cleanup" }
            noInterrupt { p.waitFor() }
            return
}

        val killer = Killer(p.toHandle())
        noInterrupt { killer.destroyChilds() }
        catchInterrupt { sleep(5) }
        noInterrupt { killer.destroyChildsForcibly() }
        catchInterrupt { sleep(5) }
        if (p.isAlive) {
           logger.info{"Why does ${p.pid()} does not want to die?"}
        }
        noInterrupt { p.waitFor() }
    } catch (e: Exception) {
        logger.warn(e){"Clean up process failed by exception"}
    }
}



fun safeCommandExec(cmd : List<String>, outName: String, readStandardOutput : Boolean = false, checkExitCode : Boolean = true, critical: Boolean = true) : Pair<Int,String> {
    val res = safeCommandArrayExecLines(cmd.toTypedArray(), outName, readStandardOutput, checkExitCode, null, critical = critical)
    val lineList = res.second
    val sb = StringBuffer()
    lineList.forEach { l ->
        sb.appendLine(l)
    }

    return Pair(res.first, sb.toString())
}
