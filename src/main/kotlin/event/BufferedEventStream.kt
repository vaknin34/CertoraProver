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

import java.util.*
import java.util.concurrent.TimeUnit
import kotlin.collections.ArrayDeque
import kotlin.concurrent.schedule
import kotlin.time.Duration
import kotlin.time.DurationUnit
import kotlin.time.ExperimentalTime
import kotlin.time.toDurationUnit

interface TimeStamper {
    fun  getCurrentTime(): Long
    fun  getTimeUnits(): TimeUnit
}

class TimeStamperMillis: TimeStamper {
    override fun  getCurrentTime(): Long = System.currentTimeMillis()
    override fun  getTimeUnits() = TimeUnit.MILLISECONDS
}

/**
 * This class manages a list of bufferedEventStreams by periodically ensuring
 * that buffered events are flushed before they get too old. Without periodic monitoring
 * it is possible that buffered events could linger for an indefinite period of time (as they
 * would only be sent once the buffer's threshold is reached)
 */
@OptIn(ExperimentalTime::class)
class BufferedEventStreamManager(bufferedEventStreams: List<BufferedEventStream>, flushThresholdMillis: UInt) {
    init {
        // timer goes off at twice the rate (half the period) of the flush rate so that we don't overshoot
        // the delay (ie wait 2 * flushThresholdMillis before we flush, instead of 1 * flushThresholdMillis)
        val timerName = "BufferedEventStreamManager_" + hashCode().toString().take(5)
        Timer(timerName ).schedule(0, (flushThresholdMillis / 2u).toLong() /*ms*/)
        {
            bufferedEventStreams.forEach {
                val flushThreshold = Duration.convert(flushThresholdMillis.toDouble(), DurationUnit.MILLISECONDS,
                    it.timeStamper.getTimeUnits().toDurationUnit()).toUInt()  // convert millis to native bufferstream timestamp units
                it.flushStream(flushThreshold)
            }
        }
    }
}

/**
 *   Abstract Base Class containing logic for buffering generic events and
 *   sending them to their destinations (determined by concrete class implementation).
 *   Since any thread is capable of buffering events, a mutex is employed to maintain the
 *   integrity of the buffer. Events are buffered until a configurable batch size is
 *   reached, then they are sent. The buffer is periodically monitored by the
 *   EventReporter class so that if the number of buffered events hasn't accumulated yet
 *   to batch size but there are still some events that have been sitting in the buffer
 *   for some (predetermined) time, those events will be flushed out.
 */
abstract class BufferedEventStream(
    private val batchSize: Int,
    val timeStamper: TimeStamper = TimeStamperMillis()
) : EventStreamBase, AutoCloseable {
    private val eventsBuffer: ArrayDeque<Pair<EventBase<*>, Long /*timestamp*/>> = ArrayDeque()

    fun addEvents(evts: List<EventBase<*>>) {
        val eventsToSend: ArrayDeque<EventBase<*>> = ArrayDeque<EventBase<*>>()
        synchronized(this) { // lock the events buffer. multiple threads may add events.
            // Timestamp and enqueue the input events
            for (evt in evts)
                eventsBuffer.addLast(Pair(evt, timeStamper.getCurrentTime()))
            // Dequeue N batches
            while (eventsBuffer.size >= batchSize) {
                repeat(batchSize) {
                    eventsToSend.addLast(eventsBuffer.removeFirst().first)
                }
            }
        }

        // at this point, the size of [eventsToSend] is some multiple of [batchSize] (or it's empty)
        eventsToSend.chunked(batchSize).forEach(::sendEvents)
    }

    // If we haven't sent any messages in flushThreshold (units of time are the same as getCurrentTime() units)
    // then send over what we have
    fun flushStream(flushThreshold: UInt = 0u) {
        val eventsToSend: ArrayDeque<EventBase<*>> = ArrayDeque<EventBase<*>>()
        synchronized(this) {// Lock the events buffer. Multiple threads may access buffer concurrently.
            // If we have old events in the event buffer, flush the buffer.
            if (!eventsBuffer.isEmpty() &&
                timeStamper.getCurrentTime() - eventsBuffer.first().second >= flushThreshold.toLong()
            ) {
                while (!eventsBuffer.isEmpty()) {
                    eventsToSend.addLast(eventsBuffer.removeFirst().first)
                }
            }
        }
        if (!eventsToSend.isEmpty()) {
            sendEvents(eventsToSend)   // will need to be overridden by inheriting class
        }
    }

    // Flush everything in the buffer
    override fun close() {
        flushStream()
    }
}
