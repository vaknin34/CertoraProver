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

package smtlibutils.cmdprocessor

import datastructures.stdcollections.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.runInterruptible
import log.*
import smt.SmtDumpEnum
import smtlibutils.algorithms.SubProcessInteraction
import smtlibutils.data.Cmd
import smtlibutils.data.Logic
import smtlibutils.data.SatResult
import utils.*
import java.io.BufferedReader
import java.io.File
import java.io.IOException
import java.io.StringWriter
import java.io.Writer
import java.nio.channels.ClosedByInterruptException
import java.nio.channels.spi.AbstractInterruptibleChannel
import java.util.concurrent.TimeUnit
import kotlin.jvm.optionals.toList

private val logger = Logger(SMTLIBUtilsLoggerTypes.SMT_CMDPROCESSOR)

private class InterruptibleProcess(val process: Process, val dumpFilename: String? = null) : AbstractInterruptibleChannel() {
    override fun implCloseChannel() {
        process.destroyForcibly()
        writeBoilerplate { ";; closing" }
        dumpStream?.let {
            when (InjectedDependencies().smt_dumpAll()) {
                SmtDumpEnum.DISABLED -> Unit
                SmtDumpEnum.TOFILE -> {
                    it.flush()
                    it.close()
                    // remove file if it only contains boilerplate
                    File(dumpFilename!!).let { file ->
                        if (file.length() <= dumpBoilerplate) {
                            file.delete()
                        }
                    }
                }
                SmtDumpEnum.TOLOG ->
                    runIf((it as StringWriter).buffer.length > dumpBoilerplate) {
                        logger.error { "Dumping SMT transcript:\n${it}" }
                    }
            }
        }
    }

    private val procInput = process.outputStream.bufferedWriter()
    private val procOutput = process.inputStream.bufferedReader()
    private val procError = process.errorStream.bufferedReader()
    /** Number of character written as boilerplate, used to figure out whether the dump file is essentially empty  */
    private var dumpBoilerplate: Int = 0
    /** The dump file stream, if dumping is enabled */
    private val dumpStream = when (InjectedDependencies().smt_dumpAll()) {
        SmtDumpEnum.DISABLED -> null
        SmtDumpEnum.TOFILE -> dumpFilename?.let { File(it) }?.outputStream()?.writer()?.buffered()
        SmtDumpEnum.TOLOG -> StringWriter()
    }

    private fun Writer.writeln(str: String) {
        write(str)
        write("\n")
    }

    /** write boilerplate to the dump file, change [dumpBoilerplate] accordingly */
    private fun writeBoilerplate(msg: () -> String) {
        dumpStream?.let {
            val m = msg()
            dumpBoilerplate += m.length + 1
            it.writeln(m)
        }
    }

    init {
        writeBoilerplate { ";; ${this.process.info().commandLine().toList().joinToString(" ")}" }
        writeBoilerplate { ";; pid = ${this.process.pid()}" }
    }

    /**
     * Dump [e] to the dump file opened if [dumpFilename] was provided. Returns [Unit?] so that users can figure out
     * whether something was dumped (and thus users can be directed to a dumpfile)
     */
    fun dumpException(e: Throwable) = try {
        dumpStream?.let {
            it.writeln(";; terminated by exception:")
            it.writeln(e.toString().replaceIndent(";; "))
        }
    } catch (e: IOException) {
        logger.warn { "Failed to write exception to ${dumpFilename}: ${e}" }
    }

    private suspend fun readLine(br: BufferedReader): String? {
        var completed = false
        try {
            begin()
            val ret = runInterruptible { br.readLine() }
            dumpStream?.let {
                if (br == procOutput) {
                    it.writeln("; out: ${ret}")
                } else {
                    it.writeln("; err: ${ret}")
                }
            }
            completed = true
            return ret
        } finally {
            end(completed)
        }
    }
    private fun readLines(br: BufferedReader): Flow<String> = flow {
        while (br.ready()) {
            readLine(br)?.let { emit(it) }
        }
    }

    fun writeln(str: String, flush: Boolean = false) {
        procInput.writeln(str)
        dumpStream?.writeln(str)
        if (flush) {
            procInput.flush()
            dumpStream?.flush()
        }
    }
    fun closeIn() = procInput.close()

    fun hasOut() = procOutput.ready()
    fun hasErr() = procError.ready()
    suspend fun readLineOut() = readLine(procOutput)
    suspend fun readLineErr() = readLine(procError)
    fun readLinesOut() = readLines(procOutput)
    fun readLinesErr() = readLines(procError)
}

/**
 * A [CmdProcessor] that interacts with an external smt solver, like z3 or cvc4.
 * Forwards all commands to the external process as strings.
 * For each command reads what the smt solver prints (e.g. "sat" after a (check-sat) command) and returns it to the
 * caller for further processing.
 * Does not return the "success" messages from the solver.
 *
 * Note: One needs to wrap this in an [ExtraCommandsCmdProcessor] if `CmdProcessor.Options.printSuccess` is to be
 * set to `true`; otherwise the solver is not configured to print the `success` messages and this
 * [InteractingCmdProcessor] will get stuck awaiting them.
 *
 * @param crashOnStdErr crash whenever the solver writes something to stdErr (not a good idea to switch on in regular usage, ususally)
 *   (smtinterpol writes misc infos, like "INFO - Assertion made context inconsistent" to stderr
 *    -- we don't want to break on that, according to Jochen it is fine to ignore stderr here, since all
 *    proper errors are also written to stdout as `(error..`  or `(unsupported ..`.
 *    note that z3 responds `unsupported` to any complicated DT logic on stderr as well (we ignore that))
 * @param crashOnError crash whenever the solver responds with `(error ...` on stdOut
 *
 */
class InteractingCmdProcessor private constructor(
    val name: String,
    override val options: CmdProcessor.Options,
    private val debugMode: Boolean = false,
    private val crashOnStdErr: Boolean = false,
    private val crashOnError: Boolean = false,
    override val solverInstanceInfo: SolverInstanceInfo,
    private val cmd: List<String>,
) : CmdProcessor {
    private val solverCommand: List<String> =
        when (solverInstanceInfo) {
            SolverInstanceInfo.None -> listOf("solver command unknown")
            is SolverInstanceInfo.Standard -> solverInstanceInfo.actualCommand
        }

    /** Collects all commands that we send to the solver. Just for debugging purposes.
     * Set to `mutableListOf()` to activate debugging.
     * Should set back to null before merging a PR. */
    private val fullHistory: MutableList<String>? = null

    private var restarts = 0
    private fun startProcess(): InterruptibleProcess {
        val dumpFile = runIf(InjectedDependencies().smt_dumpAll() == SmtDumpEnum.TOFILE) {
            restarts += 1
            InjectedDependencies().getFilePathForSmtQuery(
                name.letIf(restarts > 1) { "${it}-${restarts}" }
            )
        }

        return InterruptibleProcess(
            SubProcessInteraction.runCommand(cmd, File("."), solverInstanceInfo.critical),
            dumpFile
        )
    }

    private var processStreams = startProcess()

    init {
        if (!processStreams.process.isAlive) {
            throw SmtSolverFailedToStartException(solverInstanceInfo)
        }
    }

    companion object {
        fun fromCommand(
            name: String,
            cmd: List<String>,
            logic: Logic,
            solverInstanceInfo: SolverInstanceInfo = SolverInstanceInfo.None,
            debugOutput: Boolean = false,
            crashOnError: Boolean = false
        ): InteractingCmdProcessor =
            fromCommand(
                name,
                cmd,
                CmdProcessor.Options.Default.copy(logic = logic),
                solverInstanceInfo,
                debugOutput,
                crashOnError
            )

        fun fromCommand(
            name: String,
            cmd: List<String>,
            options: CmdProcessor.Options,
            solverInstanceInfo: SolverInstanceInfo = SolverInstanceInfo.None,
            debugOutput: Boolean = false,
            crashOnError: Boolean = false
        ): InteractingCmdProcessor {
            // spaces within [cmd] arguments indicate that the arguments were not properly split and most likely
            // result in unexpected behaviour.
            @Suppress("ForbiddenMethodCall")
            check(cmd.none { " " in it }) {
                "solver command arguments should not contain white space, but some do: \"$cmd\""
            }
            return InteractingCmdProcessor(
                name,
                options,
                debugMode = debugOutput,
                crashOnError = crashOnError,
                solverInstanceInfo = solverInstanceInfo,
                cmd = cmd,
            )
        }
    }

    private fun restartUnderlyingProcess() {
        close()
        fullHistory?.clear()
        processStreams = startProcess()
    }

    override fun processResult(cmd: Cmd): Flow<String> =
        when (cmd) {
            is Cmd.CheckSat -> checkSatInternal(cmd)
            else -> writeNonCheckSatCmd(cmd)
        }.catch { e ->
            when (e) {
                is ClosedByInterruptException -> logger.debug { "solver was cancelled" }
                else -> {
                    processStreams.dumpException(e)?.let {
                        logger.warn { "Exception while processing ${cmd}, look at ${processStreams.dumpFilename}" }
                    }
                }
            }
            throw e
        }

    /** low-level function to pass a line (typically: 1 command) to the solver */
    private suspend fun procInputWriteLine(line: String, alwaysFlush: Boolean = false) {
        try {
            fullHistory?.add(line)
            processStreams.writeln(line, alwaysFlush || options.printSuccess)
        } catch (e: IOException) {
            val stderr = consumeErr().toList().joinToString(separator = "\n")
            throw SMTSolverException(
                """
                    Couldn't write to solver process ${this.name}: ${e}
                    line to be written was: $line
                    stderr:
                        ${stderr}
                """.trimIndent(),
                e
            )
        }
    }

    private suspend fun onNull(cmd: Cmd): Nothing {
        throw IOException(
            """
                    Received `null` as a response from the solver process;
                        process.isAlive: ${processStreams.process.isAlive}.
                        smtlib command: $cmd
                        solver command: $solverCommand
                        options: $options
                        sterr:
                            ${run { consumeErr().toList().joinToString("\n\t") }}
                """.trimIndent()
        )
    }

    /**
     * throws an [IOException] when the [close] has been called before. (Not sure how to best report this, might review.)
     */
    private fun writeNonCheckSatCmd(cmd: Cmd) = flow<String> {
        // warn on push/pop for non-incremental solver
        if (!options.incremental && (cmd is Cmd.Push || cmd is Cmd.Pop)) {
            logger.warn { "Sending incremental command ${cmd} to non-incremental solver." }
        }
        if (cmd is Cmd.Reset) {
            // restart if we reset a solver that does not support it (-> bitwuzla)
            if ((solverInstanceInfo as? SolverInstanceInfo.Standard)?.solverConfig?.solverInfo?.supportsReset == false) {
                logger.warn { "solver ${solverInstanceInfo.solverConfig.solverInfo} does not support (reset), restarting the solver process instead" }
                restartUnderlyingProcess()
                return@flow
            }
        }

        procInputWriteLine(cmd.toString(), cmd.expectsResult)

        // never produces output, but might write a comment
        if (cmd is Cmd.NoOp) {
            return@flow
        }
        // some solvers do not respond to reset with success, so we just ignore it
        if (cmd is Cmd.Reset && !processStreams.hasOut()) {
            return@flow
        }

        /**
         * If the command does not expect any output, and printSuccess is false, we don't attempt to read anything.
         * In case the solver does actually respond, the output is eventually picked up by another subsequent command.
         * This might make debugging a bit harder (because the output is not associated to the right command), but we
         * can just use printSuccess in such a case.
         */
        if (!cmd.expectsResult && !options.printSuccess) {
            return@flow
        }

        val firstLine = processStreams.readLineOut()
        // the output of timeout core has two parts, a line with the sat result (often "unknown") and then the core
        // which is parenthesized; so far this is the only case where we need to read two lines looking for parentheses
        //  (which might tell us to read on)
        val nextLine =
            if (cmd is Cmd.Custom && cmd.s == "(get-timeout-core)" && firstLine in SatResult.validSatResponses) {
                processStreams.readLineOut()
            } else {
                null
            }
        var countParentheses = 0
        when (firstLine) {
            null ->
                onNull(cmd)
            "success" -> {
                // on "success" nothing else should come, just go on
            }
            "unsupported" -> {
                logger.info { "${this@InteractingCmdProcessor.name}: got 'unsupported' on $cmd" }
            }
            else -> {
                emit(firstLine)
                checkForErrorResponse(firstLine)
                firstLine.forEach { c ->
                    when (c) {
                        '(' -> countParentheses++
                        ')' -> countParentheses--
                    }
                }
                nextLine?.let { emit(it) }
                nextLine?.forEach { c ->
                    when (c) {
                        '(' -> countParentheses++
                        ')' -> countParentheses--
                    }
                }
                while (countParentheses > 0) {
                    val readLine = processStreams.readLineOut()
                    if (readLine == null) {
                        onNull(cmd)
                    } else if (readLine.contains(";; cardinality constraint:")) {
                        val currCountParentheses = countParentheses
                        do {
                            val currLine = processStreams.readLineOut()
                            currLine?.forEach { c ->
                                when (c) {
                                    '(' -> countParentheses++
                                    ')' -> countParentheses--
                                }
                            }
                        } while (countParentheses > currCountParentheses)
                    } else {
                        emit(readLine)
                        checkForErrorResponse(readLine)
                        readLine.forEach { c ->
                            when (c) {
                                '(' -> countParentheses++
                                ')' -> countParentheses--
                            }
                        }
                    }
                }
            }
        }
        checkForErrorResponse(firstLine)
    }.letIf(debugMode) {
        it.onEach { logger.debug { outputPrefix(it) } }
    }


    private fun outputPrefix(line: String) = "> $line"

    private fun checkSatInternal(cmd: Cmd.CheckSat) = flow<String> {

        consumeErr().toList()

        if (!options.printSuccess) {
            /* in this mode we don't track whatever the solver dumps to std out during processing the commands
               - we just log that here */
            processStreams.readLinesOut().onEach {
                logger.debug { "out: ${it}" }
            }.collect()
        }

        procInputWriteLine(cmd.toString(), true)

        if (options.oneOffSolver) {
            logger.debug { "terminating file solver input stream" }
            processStreams.closeIn()
        }

        var sawSatResponse = false

        var currentLine: String = try {
            processStreams.readLineOut()
                ?: run {
                    logger.debug { "throwing IOException on readLineInterruptibly (first occurrence)" }
                    checkOom(null)
                    throw IOException("reading from solver process returned \"null\" -- stream was terminated without output")
                }
        } catch (e: Exception) {
            logger.debug(e) { "caught on readLineInterruptibly (first occurrence)" }
            checkOom(null)
            throw e
        }
        emit(currentLine)
        checkForErrorResponse(currentLine)
        sawSatResponse = sawSatResponse || currentLine.trim() in SatResult.validSatResponses

        while (processStreams.hasOut() || !sawSatResponse) {
            currentLine = processStreams.readLineOut()
                ?: run {
                    logger.debug { "throwing IOException on readLineInterruptibly (second occurrence)" }
                    checkOom(null)
                    throw IOException("solver process did not respond to (check-sat) command")
                }
            checkForErrorResponse(currentLine)
            emit(currentLine)
            sawSatResponse = sawSatResponse || currentLine.trim() in SatResult.validSatResponses
            logger.debug { outputPrefix(currentLine) }
        }
    }.onEach {
        logger.debug { "check-sat result line: $it" }
    }

    private suspend fun checkForErrorResponse(currentLine: String) {
        if (processStreams.hasErr()) {
            val msg = consumeErr().toList().joinToString("\n")
            logger.debug { "$name solver process put something in the stderr pipe; ignoring it:\n $msg" }
            if (crashOnStdErr && msg.isNotEmpty()) {
                checkOom(currentLine)
                throw SMTSolverException(msg)
            }
        }

        if (crashOnError && currentLine.startsWith("(error")) {
            val errormsg = (listOf(currentLine) + processStreams.readLinesOut()).joinToString("\n")
            checkOom(currentLine)
            throw SMTSolverException(errormsg)
        }

    }

    private suspend fun checkOom(errorLine: String?) {
        // cvcX
        if (errorLine == "(error \"std::bad_alloc\")") {
            throw SMTSolverOomException(this.solverCommand)
        }

        val ec = if (!processStreams.process.isAlive) {
            processStreams.process.exitValue()
        } else {
            // process still running --> can't have oom'ed
            return
        }

        val errLines: List<String> = consumeErr().toList()
        // bitwuzla
        if (errLines.any { it == "[bzlamem] bzla_mem_malloc: out of memory in 'bzla_mem_malloc'" } &&
            ec == 1
        ) {
            throw SMTSolverOomException(this.solverCommand)
        }
        // z3
        if (errLines.any { it == "(error \"out of memory\")" } || ec == 101) {
            throw SMTSolverOomException(this.solverCommand)
        }
        // yices
        if ((errLines.any { it == "Out of memory" }) || ec == 16
        ) {
            throw SMTSolverOomException(this.solverCommand)
        }
    }

    private fun consumeErr() = processStreams.readLinesErr().onEach {
        logger.debug { "err: ${it}" }
    }

    override fun close() {
        processStreams.close()
        processStreams.process.waitFor(600, TimeUnit.MILLISECONDS)
    }

    override fun toString(): String = name

    open class SMTSolverException(val msg: String, cause: Throwable? = null) : Exception(msg, cause)

    /** thrown when smt solver crashed due to being out of memory */
    class SMTSolverOomException(val cmdLine: List<String>) :
        Exception("SMT solver process \"${cmdLine.joinToString(" ")} \" ran out of memory.")

    class SmtSolverFailedToStartException(val solverInstanceInfo: SolverInstanceInfo) :
        Exception("Failed to start smt solver; solver instance info: \"$solverInstanceInfo\"")
}

