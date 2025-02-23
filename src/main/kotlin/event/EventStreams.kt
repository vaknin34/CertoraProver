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

package event

import datastructures.stdcollections.*
import log.*
import java.io.File
import java.io.FileOutputStream

private val logger = Logger(LoggerTypes.EVENT_STREAM)

/**
 *   Interface that provides an abstraction for an Event Stream.
 *   [sendEvents] will format and output events to a concrete buffer (i.e. SQS, stdout, file, etc)
 *
 *   IMPORTANT - Make sure that [sendEvents] is implemented in a threadsafe way
 */
interface EventStreamBase {
    /** This method should be implemented in a threadsafe way */
    fun sendEvents(evts: List<EventBase<*>>)
}

/** Convenience function for sending only one event */
fun EventStreamBase.sendEvent(evt: EventBase<*>) = sendEvents(listOf(evt))

/**
 * This class represents a stream that outputs events to console.
 *  It inherits from EventStreamBase and implements the sendEvents method, which will format
 *  the event and send it out on the concrete stream.
 */
@Suppress("ForbiddenMethodCall") /** because this uses [println] */
class StdOutEventStream(val formatter: FormatterBase<String>) : EventStreamBase {
    // this function can be called concurrently by multiple threads
    @Synchronized
    override fun sendEvents(evts: List<EventBase<*>>) {
        evts.forEach {
            try {
                println(formatter.format(it))
            } catch (e: Exception) {
                Logger.alwaysError("StdOutEventStream encountered exception ${e.message} ", e)
            }
        }
    }
}

/**
 * This class represents a File stream.
 *  It inherits from EventStreamBase and implements the sendEvents method, which will format
 *  the event and send it out on the concrete stream.
 */
open class FileEventStream (
    outFileName: String,
    val formatter:  FormatterBase<String>
) : EventStreamBase, AutoCloseable {

    private val channel = FileOutputStream(File(outFileName)).bufferedWriter()

    /** This method can be called concurrently by multiple threads; Note that
     * the use of multiple stream objects all wrapping the same file would not
     * be protected by this mutex.
     */
    @Synchronized
    override fun sendEvents(evts: List<EventBase<*>>) {
        evts.forEach { event ->
            val eventFormatterResult = formatter.format(event)
            eventFormatterResult.fold(
                onSuccess = { output ->
                    try {
                        channel.write(output + System.lineSeparator())
                        channel.flush()
                    } catch (e: Exception) {
                        logger.info(e) {
                            "The output channel of a FileEventStream encountered an exception " +
                                "(channel=$channel, FileEventStream=$this)"
                        }
                    }
                },
                onFailure = {
                    logger.info(it) { "Failed to format the event $event" }
                }
            )
        }
    }

    override fun close() {
        channel.flush()
        channel.close()
    }
}
