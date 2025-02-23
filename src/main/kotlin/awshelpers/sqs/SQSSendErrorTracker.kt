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

package awshelpers.sqs

import aws.sdk.kotlin.services.sqs.model.BatchResultErrorEntry
import datastructures.NonEmptyList
import datastructures.nonEmptyListOf
import datastructures.stdcollections.*
import event.EventTopic
import log.*
import utils.partitionMap
import utils.toLeft
import utils.toRight
import java.time.Instant
import java.time.ZoneOffset
import java.time.format.DateTimeFormatter
import java.util.concurrent.atomic.AtomicInteger

private val logger = Logger(LoggerTypes.EVENT_STREAM)

/**
 * describes a send error encountered in [SQSStream].
 * [topics] is a set of all [EventTopic]s related to this error. [timestamp] is an epoch matching this error event.
 */
sealed class SQSSendError(private val topics: Set<EventTopic>, val timestamp: Long) {
    init {
        require(topics.isNotEmpty()) { "SQSSendError must have at least one associated EventTopic" }
    }

    fun formatTopics() =
        if (topics.size > 1) {
            topics.toString()
        } else {
            topics.single().toString()
        }

    /** [timestamp] is the time that [e] was caught */
    class Exception(topics: Set<EventTopic>, timestamp: Long, val e: EventReportingException) : SQSSendError(topics, timestamp) {
        constructor(topic: EventTopic, timestamp: Long, e: EventReportingException) : this(setOf(topic), timestamp, e)
    }

    /** [timestamp] is the same as in the request matching [entry] (which is the time when that request was generated) */
    class ErrorEntry(topics: Set<EventTopic>, timestamp: Long, val entry: BatchResultErrorEntry) : SQSSendError(topics, timestamp) {
        constructor(topic: EventTopic, timestamp: Long, entry: BatchResultErrorEntry) : this(setOf(topic), timestamp, entry)
    }
}

/** tracks errors encountered during send in [SQSStream.sendEvents], for the purposes of logging in suspend routines */
class SQSSendErrorTracker {
    companion object {
        /** this value must be positive */
        private const val CAPACITY: Int = 10
    }

    private val buffer = ArrayDeque<SQSSendError>(CAPACITY)
    private val totalErrorsSeen = AtomicInteger(0)

    /** insert new errors into the tracker. this is thread-safe. */
    fun addErrors(sendErrors: NonEmptyList<SQSSendError>) {
        totalErrorsSeen.getAndAdd(sendErrors.size)

        /** no point in looking at more than [CAPACITY] entries */
        val latest = sendErrors.takeLast(CAPACITY)

        synchronized(this) {
            for (error in latest) {
                /** ensure [buffer] does not exceed [CAPACITY] */
                while (buffer.size >= CAPACITY) {
                    buffer.removeFirst()
                }
                buffer.addLast(error)
            }
        }
    }

    /** insert a new error into the tracker. this is thread-safe. */
    fun addError(sendError: SQSSendError) = addErrors(nonEmptyListOf(sendError))

    /** formats the data currently contained in the tracker and logs it to the global logger. */
    fun logErrorsSummary() {
        synchronized(this) {
            if (buffer.isEmpty()) {
                Logger.always("Event reporter: all events were sent without errors", respectQuiet = true)
                return
            }

            Logger.always("Event reporter: encountered errors while sending events", respectQuiet = true)

            logger.warn { "Got a total of ${totalErrorsSeen.get()} send errors. Last ${buffer.size} are shown below." }
            logger.warn { "All dates are formatted as YYYY/MM/DD and the times are in the UTC timezone." }

            val (errorEntries, exceptions) = buffer
                .partitionMap { sendError ->
                    when (sendError) {
                        is SQSSendError.ErrorEntry -> sendError.toLeft()
                        is SQSSendError.Exception -> sendError.toRight()
                    }
                }

            /** according to AWS documentation, [BatchResultErrorEntry.code] is required, so it probably isn't null. probably. */
            val grouped = errorEntries.groupBy { it.entry.code }

            for ((errorCode, entryGroup) in grouped) {
                val errorCodeDesc = errorCode?.let { "AWS error code $it" } ?: "unknown AWS error code"

                logger.warn { "Caused by $errorCodeDesc:" }
                for (errorEntry in entryGroup) {
                    val timestamp = formatTimestamp(errorEntry.timestamp)
                    val topics = errorEntry.formatTopics()
                    val awsErrorMessageDesc = errorEntry.entry.message?.takeIf { it.isNotBlank() }?.let { "AWS error message: $it" }

                    val msg = if (awsErrorMessageDesc != null) {
                        "$timestamp - related topics: $topics $awsErrorMessageDesc"
                    } else {
                        "$timestamp - related topics: $topics"
                    }

                    logger.warn { msg }
                }
            }

            if (exceptions.isNotEmpty()) {
                logger.warn { "Caused by exceptions:" }
            }
            for (exceptionError in exceptions) {
                val timestamp = formatTimestamp(exceptionError.timestamp)
                val topics = exceptionError.formatTopics()
                logger.warn { "$timestamp - ${exceptionError.e.message} - related topics: $topics" }
            }
        }
    }
}

val sqsSendErrorTracker = SQSSendErrorTracker()

internal fun formatTimestamp(epoch: Long) = Instant
    .ofEpochMilli(epoch)
    .atZone(ZoneOffset.UTC)
    .format(DateTimeFormatter.ofPattern("uuuu-MM-dd HH:mm:ss"))
