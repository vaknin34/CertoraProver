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

@file:UseSerializers(EventBase.JobIDString::class)
package event

import kotlinx.serialization.UseSerializers
import utils.KSerializable

/**
 * Events sent for diagnosability of the cache
 */
@KSerializable
sealed class CacheEvent : EventBase<EventTopic.Cache>(){
 companion object {
        const val EVENT_STREAM_FILE = "CacheEvents.txt"
    }

    override val eventTopic = EventTopic.Cache


    @KSerializable
    data class CacheHit(val cacheKey: String) : CacheEvent() {
        override val eventTypeId: String
            get() = "CacheHit"
    }

    /**
     * Indicates number of cache files in the cacheDir when it is sent.
     * sent in the beginning and in the end
     */
    @KSerializable
    data class NumCacheFiles(val n : Int, val isStart: Boolean) : CacheEvent() {
        override val eventTypeId: String
            get() = "NumCacheFiles"
    }

    @KSerializable
    data class CacheMiss(val cacheKey: String) : CacheEvent() {
        override val eventTypeId: String
            get() = "CacheMiss"
    }

    @KSerializable
    data class CacheDirSize(val bytes: Long, val isStart: Boolean) : CacheEvent() {
        override val eventTypeId: String
            get() = "CacheDirSize"
    }
}


