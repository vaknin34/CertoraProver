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

import annotations.PollutesGlobalState
import aws.sdk.kotlin.services.sqs.SqsClient
import aws.sdk.kotlin.services.sqs.model.*
import aws.smithy.kotlin.runtime.SdkBaseException
import config.AWSConfig
import config.Config
import datastructures.NonEmptyList
import datastructures.stdcollections.*
import datastructures.toNonEmptyList
import event.*
import kotlin.time.Duration.Companion.milliseconds
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.withTimeout
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.JsonObject
import kotlinx.serialization.json.jsonObject
import log.Logger
import log.LoggerTypes
import parallel.coroutines.launchBackground
import report.EventEnvironmentVars
import utils.*
import java.util.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ConcurrentMap

private val logger = Logger(LoggerTypes.EVENT_STREAM)

/**
 * A factory for generating the group ID according to the event order policy ([EventTopic.EventOrderPolicy])
 * of [EventTopic].
 * A none-FIFO policy ([EventTopic.EventOrderPolicy.NONE]) is implemented using UUID to generate a random group ID
 * for each event.
 * FIFO-queue policy ([EventTopic.EventOrderPolicy.FIFO]) is implemented by generating the same group ID for all events
 * with the same topic. That is, the group ID is determined by [EventTopic]. It is prefixed with the current job ID
 * to enforce a fifo policy on [EventTopic] only for the current job ID (rather than on all aggregated events of
 * [EventTopic] across all jobs).
 */
object SQSGroupIdFactory {

    operator fun invoke(eventTopic: EventTopic): String =
        when (eventTopic.orderPolicy) {
            EventTopic.EventOrderPolicy.NONE -> {
                UUID.randomUUID().toString()
            }

            EventTopic.EventOrderPolicy.FIFO -> {
                "${EventEnvironmentVars.jobId}_${eventTopic.name}"
            }
        }

}

/**
 *  The concrete [FormatterBase] for the [SQSStream].
 */
class SQSFormatter : FormatterBase<SendMessageBatchRequestEntry> {
    /**
     *  This formatter formats an event object in JSON string format,
     *  but without class discriminator
     */
    private object SQSMsgBodyFormat : FormatterBase<String> {
        override fun format(e: EventBase<*>): Result<String> = runCatching {
            val serialized = Json.encodeToJsonElement(EventBase.serializer(EventTopic.serializer()), e)

            // TODO CERT-2635 we should not remove the type discriminator.
            JsonObject(serialized.jsonObject.filterNot { it.key == "type" }).toString()
        }
    }

    override fun format(e: EventBase<*>): Result<SendMessageBatchRequestEntry> {
        return SQSMsgBodyFormat.format(e).map { formattedMsgBody ->
            SendMessageBatchRequestEntry {
                messageBody = formattedMsgBody
                id = generateUUID() //this is 32 characters long, which fits this field's 80-character limit
                messageGroupId = SQSGroupIdFactory(e.eventTopic)
            }
        }
    }
}


/**
 *  This class is an implementation of [EventStreamBase], to output events to SQS queues.
 *  Takes [sqsClient] which is used to send requests and [credentials], the credentials of this stream.
 *  To send events, use [sendEvents], with a list of [EventBase] as the input parameter.
 */
@PollutesGlobalState
class SQSStream private constructor(private val sqsClient: SqsClient, private val credentials: StreamCredentials) : EventStreamBase {
    private val sqsFormatter : FormatterBase<SendMessageBatchRequestEntry> = SQSFormatter()

    /*
    TODO: This is a "versionStr" for the "Version" attribute of the messages sent by this SQSStream.
     This attribute is meant for future use, in case we need backwards compatibility, and want to have some version control.
    */
    private val versionStr = "1.0"

    private data class RequestWrapper(val req: SendMessageBatchRequestEntry, val topic: EventTopic, val timestamp: Long)

    private suspend fun sendBatchMessagesToQueue(requestWrappers: NonEmptyList<RequestWrapper>) {
        val requests = requestWrappers.map { it.req }

        val sendBatchRequest = SendMessageBatchRequest {
            entries = requests
            queueUrl = credentials.url
        }

        val result = runCatching {
            val timeout = Config.SQSEventTimeoutMilliseconds.get().milliseconds

            withTimeout(timeout) {
                //This call is thread safe, according to the AWS API documentation.
                sqsClient.sendMessageBatch(sendBatchRequest)
            }
        }

        result
            .onFailure { e ->
                val exceptionTimestamp = currentTimestamp()

                /** since this is a batch request, multiple topics may be related to this failure */
                val allTopics = requestWrappers.mapToSet { it.topic }
                val wrapped = EventReportingException.wrap(e)

                val sendError = SQSSendError.Exception(allTopics, exceptionTimestamp, wrapped)
                sqsSendErrorTracker.addError(sendError)
            }.onSuccess { response ->
                val errorEntries = errorEntriesFromBatch(response.failed.orEmpty(), requestWrappers)
                if (errorEntries != null) {
                    sqsSendErrorTracker.addErrors(errorEntries)

                    val idsOfFailedRequests = errorEntries.map { it.entry.id }
                    logger.info { "Failed to send messages with the following ids: $idsOfFailedRequests" }
                }

                val successful = response.successful.orEmpty()
                logger.debug { "Sending ${requests.size} batch messages. ${successful.size} sent successfully." }
            }
    }

    /** returns a [SQSSendError.ErrorEntry] for each [BatchResultErrorEntry] in [failed], if a matching request was found in [requestWrappers] */
    private fun errorEntriesFromBatch(
        failed: List<BatchResultErrorEntry>,
        requestWrappers: NonEmptyList<RequestWrapper>
    ): NonEmptyList<SQSSendError.ErrorEntry>? =
        failed
            .mapNotNull { errorEntry ->
                requestWrappers
                    .find { it.req.id == errorEntry.id }
                    ?.let { SQSSendError.ErrorEntry(it.topic, it.timestamp, errorEntry) }
            }
            .toNonEmptyList()

    /**
     * This is the method used to send events to the [SQSStream], and is an implementation of [EventStreamBase.sendEvents].
     * As required for all implementations of the [sendEvents] method, this method is threadsafe.
     * This method is non-blocking, the events are sent asynchronously using the [Dispatchers.IO] thread pool.
     * This method also adds the following messageAttributes to the messages sent to
     * the queue (which can be overridden if they're included in [SendMessageBatchRequestEntry.messageAttributes]):
     * Version - The version string ([versionStr]).
     * EventTypeID - The id of the type of the event which was sent to the stream.
     * Timestamp - The timestamp when the event was sent to the stream.
     */
    override fun sendEvents(evts: List<EventBase<*>>) {
        val (requestWrappers, errors) = processEvents(evts)

        if (errors != null) {
            sqsSendErrorTracker.addErrors(errors)
        }

        if (requestWrappers != null) {
            requestWrappers.forEach(::logOnWrapperCreation)

            /**
              Send messages. note that [launchBackground] will propagate any uncaught exception to our main entrypoint.
             */
            launchBackground("Send SQS events") {
                sendBatchMessagesToQueue(requestWrappers)
            }
        }
    }

    /** process each event in [events] into either a new [RequestWrapper] or a [SQSSendError] if an exception was caught */
    private fun processEvents(events: List<EventBase<*>>): Pair<NonEmptyList<RequestWrapper>?, NonEmptyList<SQSSendError>?> {
        val requestWrappers = mutableListOf<RequestWrapper>()
        val errors = mutableListOf<SQSSendError>()

        for (evt in events) {
            val topic = evt.eventTopic
            val timestamp = currentTimestamp()

            val formatted = sqsFormatter.format(evt)

            formatted
                .onSuccess { requestTemplate ->
                    val newRequest = createNewMessageRequest(requestTemplate, evt, timestamp)
                    val wrapper = RequestWrapper(newRequest, topic, timestamp)
                    requestWrappers.add(wrapper)
                }.onFailure { e ->
                    val wrapped = EventReportingException.wrap(e)
                    val sendError = SQSSendError.Exception(topic, timestamp, wrapped)
                    errors.add(sendError)
                }
        }

        return Pair(
            requestWrappers.toNonEmptyList(),
            errors.toNonEmptyList()
        )
    }

    /** generate a new request fot [evt] based on [requestTemplate] */
    private fun createNewMessageRequest(
        requestTemplate: SendMessageBatchRequestEntry,
        evt: EventBase<*>,
        timestamp: Long
    ): SendMessageBatchRequestEntry {
        val addedAttributes = mapOf(
            "Version" to MessageAttributeValue {
                dataType = "String"
                stringValue = versionStr
            },
            "EventTypeID" to MessageAttributeValue {
                dataType = "String"
                stringValue = evt.eventTypeId
            },
            "Timestamp" to MessageAttributeValue {
                dataType = "Number"
                stringValue = timestamp.toString()
            }
        )

        val newAttributes = requestTemplate.messageAttributes.orEmpty() + addedAttributes

        return requestTemplate.copy { messageAttributes = newAttributes }
    }

    private fun logOnWrapperCreation(wrapper: RequestWrapper) {
        val msg = when {
            wrapper.req.messageBody != null -> "Sending message: ${wrapper.req.messageBody}"
            wrapper.req.id != null -> "New request with id ${wrapper.req.id} was created without a body"
            else -> "New request created without body or id"
        }

        logger.debug { msg }
    }

    /**
     * SQSStreamFactory
     * A singleton that creates the one and only instance of the SQS Queue
     * which is identified by queue name
     */
    companion object SQSStreamFactory {
        private val sqsMap: ConcurrentMap<String, Result<SQSStream>>  = ConcurrentHashMap()
        private val sqsRegion: String = AWSConfig.AWSRegion.get()

        suspend fun fetchSQSStream(queueName: String) : Result<SQSStream> =
            sqsMap.getOrPut(queueName) {
                val sqsClient = SqsClient { region = sqsRegion }

                @Suppress("SuspendFunSwallowedCancellation") // handled below
                runCatching {
                    val credentials = StreamCredentials(queueName, sqsClient)
                    SQSStream(sqsClient, credentials)
                }.onFailure {
                    if (it is CancellationException) { throw it }
                }
            }
    }
}

/** Contains the [name] and [url] of some [SQSStream]. Since getting these values may throw, this is initialized separately. */
private data class StreamCredentials(val name: String, val url: String) {
    companion object {
        const val MAX_NAME_LENGTH = 80

        operator suspend fun invoke(name: String, sqsClient: SqsClient): StreamCredentials {
            require(name.length <= MAX_NAME_LENGTH) {
                "The name of the queue $name was too long! Must be $MAX_NAME_LENGTH characters at most!"
            }

            val request = GetQueueUrlRequest { queueName = name }

            val queueUrl = try {
                val response = sqsClient.getQueueUrl(request)
                response.queueUrl
            } catch (e: SdkBaseException) {
                throw EventReportingException.wrap(e)
            }

            check(queueUrl != null) { "The queueUrl returned by getQueueUrl for queueName $name was null." }
            return StreamCredentials(name, queueUrl)
        }
    }
}

