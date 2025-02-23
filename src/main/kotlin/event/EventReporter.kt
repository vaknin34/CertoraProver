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
import log.Logger
import log.LoggerTypes

private val logger = Logger(LoggerTypes.EVENT_STREAM)

/**
 * This is the class that will be the interface to all classes/methods in the system
 *   that seek to report events. It takes as input a TopicManager;
 *   in this way we associate an event with its stream(s). Note that one event may be
 *   reported out on to multiple streams (we could for example report the same event in
 *   two different ways; once to SQS and once to log. The same
 *   event would be formatted differently each time). To stream an event(s), the caller would
 *   invoke reportEvents with a list of events. Those events would then be distributed on to
 *   their associated streams.
 */
open class EventReporter(private val eventStreamMapper: EventStreamMapper) {
    /** May be called from multiple threads concurrently
     * @param events - List of events to report
     */
    open fun reportEvents(events: List<EventBase<*>>) {
        val topicsToEvents: Map<EventTopic, List<EventBase<*>>> = events.groupBy { it.eventTopic }
        topicsToEvents.forEachEntry { (topic, eventsList) ->
            val topicStreams = eventStreamMapper.streamsOf(topic)

            for (stream in topicStreams) {
                logger.debug {
                    "About to emit ${eventsList.size} events to the stream $stream for topic ${topic.name}"
                }

                when (stream) {
                    is BufferedEventStream -> stream.addEvents(eventsList)
                    else -> stream.sendEvents(eventsList)
                }
            }
        }
    }
}

fun EventReporter.reportEvent(event: EventBase<*>) = reportEvents(listOf(event))

/** Convenience subclass for an [EventReporter] with an empty [EventStreamMapper] */
object EmptyEventReporter : EventReporter(EventStreamMapper()) {
    override fun reportEvents(events: List<EventBase<*>>) {}
}
