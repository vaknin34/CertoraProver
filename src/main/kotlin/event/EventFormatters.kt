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

import kotlinx.serialization.json.Json

/**
 *  This is the interface that is inherited by all concrete formatters. See
 *  https://docs.google.com/document/d/17FPNGfZMh55AAtMwD-iEcfAU_AobOdDJwT_4UfbTssc/edit
 *  for more details.
 */
interface FormatterBase<T> {
    fun format(e: EventBase<EventTopic>) : Result<T>
}

object JsonFormatter : FormatterBase<String> {
    val jsonFormatter = Json { classDiscriminator = "EventTypeId" }
    override fun format(e: EventBase<*>): Result<String> = runCatching {
        jsonFormatter.encodeToString(EventBase.serializer(EventTopic.serializer()), e)
    }
}
