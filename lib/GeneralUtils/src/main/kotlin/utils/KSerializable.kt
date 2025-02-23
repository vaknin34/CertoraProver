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

package utils

/**
 * Convenience alias to make it easier to disambiguate between [kotlinx.serialization.Serializable] and
 * [java.io.Serializable].
 */
typealias KSerializable = kotlinx.serialization.Serializable

/**
 * Convenience alias to make it easier to disambiguate between [kotlinx.serialization.Transient] and
 * [java.lang.Transient].
 */
typealias KTransient = kotlinx.serialization.Transient
