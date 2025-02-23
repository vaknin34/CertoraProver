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

/**
 * An object that may be reportable by the event's framework.
 * Allows adding shared  or custom attributes and methods for different events.
 *
 */
interface EventReportable

/**
 * Marks that a class can be reported as an 'attribute' ([asEventAttribute]) of an event.
 */
interface ReportableAsEventAttribute<T: EventAttribute>: EventReportable {
    val asEventAttribute: T
}

interface EventAttribute

interface EventAttributeWithStringRepr: EventAttribute {
    val stringRepr: String
}
