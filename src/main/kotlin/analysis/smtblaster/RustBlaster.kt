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

package analysis.rustblaster


import config.Config
import log.*
import java.io.Closeable
import java.util.concurrent.CompletableFuture
import java.util.concurrent.Executors
import java.util.concurrent.SynchronousQueue
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicInteger

private val pLogger = Logger(GeneralUtilsLoggerTypes.PARALLEL)

// This pool keeps a set of egg executables running so that we can perform queries to the egg solver
// One use case is in LogicalEquality, which asks the egg solver (fried-egg) if two small programs are equal
class RustBlasterPool(
    private val workers: Int = System.getProperty("cvt.default.parallelism")?.toIntOrNull() ?: Runtime.getRuntime()
    .availableProcessors(),
    poolName: String = "rustBlasterPool",
    isDaemon: Boolean = false
) : Closeable {
    private val uniquePoolName = "${poolName}_${poolCtr.incrementAndGet()}"

    private data class Query(
        val query: String,
        val result: CompletableFuture<String>,
    )

    companion object {
        /** Used to disambiguate the (default) names of different [RustBlasterPool] instances. */
        val poolCtr: AtomicInteger = AtomicInteger(0)
    }

    private val channel = SynchronousQueue<Query>()

    private val workerPool = if(isDaemon) {
        Executors.newFixedThreadPool(2 * workers + 1) {
            val t = Thread(it)
            t.isDaemon = true
            t
        }
    } else {
            Executors.newFixedThreadPool(2 * workers + 1)
        }


    init {
        start()
    }

    private inner class RustWorker(val name: String) : Runnable {
        private val process = ProcessBuilder(*listOf("tac_optimizer").toTypedArray())
        .redirectOutput(ProcessBuilder.Redirect.PIPE)
        .redirectError(if (Config.TestMode.get()) ProcessBuilder.Redirect.INHERIT else ProcessBuilder.Redirect.PIPE)
        .start()

        private val procInput = process.outputStream.bufferedWriter()
        private val procOutput = process.inputStream.bufferedReader()


        override fun run() {
          while (true) {
              val x = try {
                  channel.take()
              } catch (e: InterruptedException) {
                  shutdown()
                  return
              }
              pLogger.debug {
                  "Running command in thread ${Thread.currentThread()}"
              }
              check(x is Query)

              try {
                  procInput.write(x.query);
                  procInput.write("\n");
                  procInput.flush()

                  val eggStr = procOutput.readLine()

                  x.result.complete(eggStr)
              } catch (e : Exception) {
                  x.result.completeExceptionally(e)
              }
          }
        }

        private fun shutdown() {
            procInput.close()
            procOutput.close()
            process.destroy()
        }
    }

    private fun start() {
        for (i in 0..workers) {
            workerPool.submit(RustWorker("${uniquePoolName}_worker_$i"))
        }
    }

    override fun close() {
        workerPool.shutdownNow()
        workerPool.awaitTermination(400, TimeUnit.MILLISECONDS)
    }

    fun blast(query: String): String {
        pLogger.debug {
            "About to submit and stall in thread ${Thread.currentThread()}"
        }
        val container = CompletableFuture<String>()
        val res = workerPool.submit(Runnable {
            channel.put(Query(query, container))
        })
        res.get()
        return container.get()
    }
}
