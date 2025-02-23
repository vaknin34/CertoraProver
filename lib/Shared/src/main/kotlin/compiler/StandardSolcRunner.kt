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

package compiler

import compiler.data.Input
import compiler.data.Output
import kotlinx.serialization.json.Json
import log.Logger
import log.LoggerTypes
import java.io.File
import java.nio.file.Path
import java.util.concurrent.TimeUnit
import kotlin.io.path.absolutePathString

private val logger = Logger(LoggerTypes.COMMON)

class StandardSolcRunner(solcExecutable: String, allowPaths: List<String>, val runDir: Path? = null) {
    private val cmdList : Array<String>
    init {
        val build = mutableListOf(solcExecutable, "--standard-json")
        if(allowPaths.isNotEmpty()) {
            build+= "--allow-paths"
            build+= allowPaths.joinToString(",")
        }
        cmdList = build.toTypedArray()
    }

    private val json = Json {
        ignoreUnknownKeys = true
    }

    fun run(inputParams: Input) : Output? {
        val process = try {
            val builder1 = ProcessBuilder(*cmdList)
            val builder2 = if (runDir != null) {
                builder1.directory(File(runDir.absolutePathString()))
            } else {
                builder1
            }
            builder2.start()
        } catch(e: Exception) {
            logger.error(e) {
                "Failed to start command ${cmdList.joinToString(" ")}"
            }
            return null
        }
        val inputJson = json.encodeToString(Input.serializer(), inputParams).toString()
        logger.trace {
            "Sending input $inputJson to solidity"
        }
        process.outputStream.use {
            try {
                it.write(inputJson.toByteArray())
            } catch(e: Exception) {
                logger.error(e) {
                    "Failed to write to solidity process, dying"
                }
                process.destroyForcibly()
                return null
            }
        }
        process.outputStream.flush()
        // solidity waits for std in to be closed...
        process.outputStream.close()
        val reader = process.inputStream.reader().buffered()
        try {
            process.waitFor(1L, TimeUnit.SECONDS)
        } catch(e: Exception) {
            logger.error(e) {
                "Failure while waiting for the solidity compiler"
            }
            process.destroyForcibly()
            return null
        }
        val result = try {
            reader.readText()
        } catch(e: Exception) {
            logger.error(e) {
                "Failed while reading standard output"
            }
            return null
        } finally {
            process.destroy()
        }
        logger.trace {
            "Got back raw output $result"
        }
        return try {
            json.decodeFromString(Output.serializer(), result)
        } catch (e: Exception) {
            logger.error(e) {
                "Failed to parse json returned from call for ${cmdList.toList()} with $inputParams. \n" +
                "Tried parsing: $result"
            }
            null
        }
    }
}
