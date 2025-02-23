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

package sbf.domains

/** A trivial three-valued Boolean **/
data class TriBoolean(val value: Boolean?) {
    companion object {
        private val topTB = TriBoolean(null)
        fun makeTop(): TriBoolean {
            return topTB
        }
    }

    fun isTop(): Boolean {
        return value == null
    }

    fun isTrue(): Boolean {
        return value != null && value
    }

    fun isFalse(): Boolean {
        return value != null && !value
    }

    fun and(other: TriBoolean ): TriBoolean {
        return if (value == null) {
            when (other.value) {
                null -> this
                true -> this
                false -> TriBoolean(false)
            }
        } else if (other.value == null) {
            when (value) {
                true -> other
                false -> TriBoolean(false)
            }
        } else {
            TriBoolean(value && other.value)
        }
    }

    fun or(other: TriBoolean ): TriBoolean {
        return if (value == null) {
            when (other.value) {
                null -> this
                true -> TriBoolean(true)
                false -> this
            }
        } else if (other.value == null) {
            when (value) {
                true -> TriBoolean(true)
                false -> other
            }
        } else {
            TriBoolean(value || other.value)
        }
    }

    fun lessOrEqual(other: TriBoolean): Boolean {
        return if (other.isTop()) {
            true
        } else if (isTop()) {
            false
        } else {
            value!! == other.value!!
        }
    }

    override fun toString(): String {
        return when (value) {
            null -> "top"
            true -> "true"
            false -> "false"
        }
    }
}
