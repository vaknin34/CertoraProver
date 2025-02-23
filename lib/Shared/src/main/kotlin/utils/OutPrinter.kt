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

import config.Config.ShowPingInStderr
import log.*
import java.io.OutputStream
import java.io.OutputStreamWriter
import java.io.PrintWriter
import java.lang.management.*
import kotlin.system.exitProcess
import kotlin.time.Duration

object OutPrinter {

    private val _file = ArtifactFileUtils.getResultFile()
    private var isInit = false

    private var resultsFile: PrintWriter = PrintWriter(OutputStreamWriter(OutputStream.nullOutputStream()))

    // call from main thread before there are other calls to this class, and after artifact manager was determined
    fun init(customPrintWriter : PrintWriter? = null) {
        if (!isInit) {
            isInit = true
            if (customPrintWriter == null) {
                ArtifactManagerFactory().registerArtifact(_file)
                resultsFile = PrintWriter(ArtifactManagerFactory().getArtifactHandle(_file))
            } else {
                resultsFile = customPrintWriter
            }
        }
    }

    fun close() {
        if (isInit) {
            resultsFile.close()
            isInit = false
        }
    }

    fun printWarningToScreen(x: String) {
        @Suppress("ForbiddenMethodCall")
        println("Warning: $x")
    }

    fun printErrorToScreen(x: String) {
        @Suppress("ForbiddenMethodCall")
        println("Error: $x")
    }

    fun print(x: String, toStdout: Boolean = false) = print(null, x, toStdout)
    fun print(t: Throwable?, x : String, toStdout : Boolean = false) {
        if (toStdout) {
            println(x)
        }
        try {
            synchronized(resultsFile) {
                resultsFile.appendLine(x)
                t?.printStackTrace(resultsFile)
            }
            resultsFile.flush()
        } catch (_: IllegalStateException) {
            // skip if it's too early to print
        }
    }


    /**
     * For printing out the thread dump on a timeout.
     */
    fun dumpThreads(filename: String) {
        ArtifactManagerFactory().registerArtifact(filename)
        ArtifactManagerFactory().getArtifactHandle(filename).use { file ->
            val threadMXBean: ThreadMXBean = ManagementFactory.getThreadMXBean()
            for (threadInfo in threadMXBean.dumpAllThreads(true, true)) {
                file.append(threadInfo.toStringFull())
            }
        }
    }

    /**
     * John: Helper for printing out the COMPLETE thread dump (instead of just the MAX_LIMIT
     * stack frames of the dump)
     */
    private fun ThreadInfo.toStringFull(): String? {
        val sb = StringBuilder(
          "\"" + getThreadName() + "\"" +
            (if (isDaemon) { " daemon" } else { "" }) +
            " prio=" + priority +
            " Id=" + getThreadId() + " " +
            getThreadState()
        )
        if (getLockName() != null) {
            sb.append(" on " + getLockName())
        }
        if (getLockOwnerName() != null) {
            sb.append(
              (" owned by \"" + getLockOwnerName() +
                "\" Id=" + getLockOwnerId())
            )
        }
        if (isSuspended()) {
            sb.append(" (suspended)")
        }
        if (isInNative()) {
            sb.append(" (in native)")
        }
        sb.append('\n')
        var i = 0
        while (i < stackTrace.size) {
            val ste: StackTraceElement = stackTrace.get(i)
            sb.append("\tat $ste")
            sb.append('\n')
            if (i == 0 && getLockInfo() != null) {
                val ts: Thread.State = getThreadState()
                when (ts) {
                    Thread.State.BLOCKED -> {
                        sb.append("\t-  blocked on " + getLockInfo())
                        sb.append('\n')
                    }
                    Thread.State.WAITING -> {
                        sb.append("\t-  waiting on " + getLockInfo())
                        sb.append('\n')
                    }
                    Thread.State.TIMED_WAITING -> {
                        sb.append("\t-  waiting on " + getLockInfo())
                        sb.append('\n')
                    }
                    else -> {}
                }
            }
            for (mi: MonitorInfo in lockedMonitors) {
                if (mi.lockedStackDepth == i) {
                    sb.append("\t-  locked $mi")
                    sb.append('\n')
                }
            }
            i++
        }
        if (i < stackTrace.size) {
            sb.append("\t...")
            sb.append('\n')
        }
        val locks: Array<LockInfo> = getLockedSynchronizers()
        if (locks.size > 0) {
            sb.append("\n\tNumber of locked synchronizers = " + locks.size)
            sb.append('\n')
            for (li: LockInfo in locks) {
                sb.append("\t- $li")
                sb.append('\n')
            }
        }
        sb.append('\n')
        return sb.toString()
    }
}


class TimePing(
    val frequency: Duration,
    val doPing: Boolean = true,
    val timeout: Duration? = null,
    val startTime: TimeSinceStart = TimeSinceStart(),
) : Thread() {
    companion object {
        val progressReports = mutableListOf<() -> String>()

        fun registerReport(f: () -> String) {
            synchronized(this) {
                progressReports.add(f)
            }
        }
    }

    val elapsedMinutes get() = startTime.elapsedNow().inWholeMinutes

    override fun run() {

        Logger.always("Start ${java.util.Calendar.getInstance().time}", respectQuiet = false)

        try {
            while (true) {
                sleep(frequency.inWholeMilliseconds)
                if (doPing) {
                    val msg = "Ping ${elapsedMinutes}m - ${progressReports.map { it() }
                        .joinToString(";")}"
                    Logger.always(msg, respectQuiet = false)
                    if (ShowPingInStderr.get()) {
                        System.err.println(msg)
                    }
                }
                if (timeout != null && startTime.elapsedNow() > timeout) {
                    throw TimeCheckException()
                }
            }
        } catch (_: InterruptedException) {
        } finally {
            Logger.always("Done ${elapsedMinutes}m", respectQuiet = false)
        }
    }

    fun bye() {
        try {
            this.interrupt()
        } catch (e : Exception) {
            try {
                Logger.alwaysError("Got error $e when interrupting")
            } catch (_: Exception) {
                // Logger.always exception can cause us to enter an infinite loop in EntryPoint
            }
            exitProcess(1)
        }
    }
}

