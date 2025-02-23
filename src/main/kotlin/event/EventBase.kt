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

import event.EventBase.JobIDString.serialize
import kotlinx.serialization.KSerializer
import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import report.EventEnvironmentVars
import utils.HasKSerializable
import utils.KSerializable


/**
 *  Base class that is inherited by all concrete events.
 *  @property [jobId] the identifier of the execution in which this event was sent.
 *  @property [eventTypeId] the class name of the event.
 */
@KSerializable
sealed class EventBase<out T: EventTopic> : HasKSerializable {
    /**
     * unique job id per execution.
     */
    open val jobId: EventEnvironmentVars.EventEnvValue = EventEnvironmentVars.jobId

    /**
     * unique user id per execution.
     */
    open val userId: EventEnvironmentVars.EventEnvValue = EventEnvironmentVars.userId

    /**
     * The topic which the event is associated with.
     */
    abstract val eventTopic: T

    /**
     * Identifier of the event.
     */
    abstract val eventTypeId: String

    /**
     * Emits or reports this event by visiting the given [reporter].
     */
    fun emit(reporter: EventReporter) {
        reporter.reportEvent(this)
    }

    /**
     * Used in all EventBase implementation.
     * Supports only in serialization, and only string value is taken in [serialize]
     */
    object JobIDString : KSerializer<EventEnvironmentVars.EventEnvValue> {
        override val descriptor: SerialDescriptor = String.serializer().descriptor
        override fun deserialize(decoder: Decoder): EventEnvironmentVars.EventEnvValue {
            throw NotImplementedError("not supposed to")
        }

        override fun serialize(encoder: Encoder, value: EventEnvironmentVars.EventEnvValue) {
            encoder.encodeString(value.value)
        }
    }
}

@KSerializable
sealed class EventTopic : HasKSerializable {

    enum class EventOrderPolicy {
        NONE,
        FIFO
        ;
    }

    abstract val orderPolicy: EventOrderPolicy
    abstract val name: String

    override fun toString() = name

    @KSerializable
    object CVT: EventTopic() {

        override val name: String
            get() = "CVT"
        override val orderPolicy: EventOrderPolicy
            get() = EventOrderPolicy.NONE
    }

    @KSerializable
    object Cache: EventTopic() {
        override val orderPolicy: EventOrderPolicy
            get() = EventOrderPolicy.NONE
        override val name: String
            get() = "Cache"

    }

    @KSerializable
    object SMT: EventTopic() {
        override val name: String
            get() = "SMT"

        override val orderPolicy: EventOrderPolicy
            get() = EventOrderPolicy.NONE
    }

    @KSerializable
    object Rule: EventTopic() {
        override val name: String
            get() = "Rule"

        override val orderPolicy: EventOrderPolicy
            get() = EventOrderPolicy.NONE
    }

    @KSerializable
    object TestFifo: EventTopic() {
        override val name: String
            get() = "TestFifo"

        override val orderPolicy: EventOrderPolicy
            get() = EventOrderPolicy.FIFO
    }
    @KSerializable
    object Test: EventTopic() {
        override val name: String
            get() = "Test"

        override val orderPolicy: EventOrderPolicy
            get() = EventOrderPolicy.NONE
    }

}
