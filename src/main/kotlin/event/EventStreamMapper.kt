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
 * The EventStreamMapper class associates event topics with streams.
 * An event topic, that can be linked to multiple event type can be associated with multiple streams
 * In this way, classes of events - identified by their topics, can be associated
 * with streams in a flexible manner.
 */
class EventStreamMapper(
    eventTopicToStreamResults: Map<EventTopic, Set<Result<EventStreamBase>?>> = emptyMap()
) {
    private val eventTopicToStreams: Map<EventTopic, Set<EventStreamBase>>

    init {
        eventTopicToStreams = mutableMapOf()

        eventTopicToStreamResults.forEachEntry { (topic, streams) ->
            val validStreams = mutableSetOf<EventStreamBase>()

            for (stream in streams) {
                if (stream != null) {
                    stream
                        .onSuccess { validStreams.add(it) }
                        .onFailure { logger.warn(it) { "Stream for topic $topic had an exception and will not be available" } }
                }
            }

            eventTopicToStreams[topic] = validStreams
        }
    }

    /**
     * Given an [EventTopic], return all event streams that are associated with that topic
     * Note: streams will not be duplicated.
     */
    fun streamsOf(topic: EventTopic) = eventTopicToStreams[topic].orEmpty()
}
