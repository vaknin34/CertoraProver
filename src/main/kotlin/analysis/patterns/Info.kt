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

package analysis.patterns

import analysis.LTACCmd
import com.certora.collect.*


/**
 * A class that holds an immutable map from typed keys to their values, which are enforced to be of that type. It also
 * holds one [LTACCmd] as a special value. Operations are defined as extension functions on a nullable receiver
 * and many times return [Info]?, That is so they can be chained, and propagate null values transparently.
 * This class is used for collecting information while using the pattern matcher.
 *
 * This class should never be serialized, as it uses a [TreapMap] yet the keys are not `Treapable`.
 */
data class Info(
    @Suppress("Treapability")
    private val backing: TreapMap<InfoKey<*>, Any?> = treapMapOf(),
    private val lastCmd: LTACCmd? = null
) {
    operator fun contains(key: InfoKey<*>) = key in backing

    override fun toString() =
        backing.toList().joinToString("\n") { (k, v) -> "$k = $v" } +
            lastCmd?.let { "\n${it.ptr} : ${it.cmd.toStringNoMeta()}" }.orEmpty()

    fun getUntyped(k : InfoKey<*>) = backing[k]

    companion object {
        operator fun <T> invoke(key: InfoKey<T>?, v: T) =
            Info().set(key, v)

        fun Info.setLastCmd(cmd: LTACCmd) =
            copy(lastCmd = cmd)

        /**
         * Sets [k] to be [v], and returns the new [Info], but [k] is already set to some other value, in which case returns null.
         * If [k] is null, it just returns [this].
         */
        operator fun <T> Info?.set(k: InfoKey<T>?, v: T?) =
            when {
                this == null -> null
                k == null -> this
                k in backing && backing[k] != v -> null
                else -> copy(backing = backing.put(k, v))
            }

        /** Saves the last command as the value of [k] */
        fun Info.lastCmd(k: InfoKey<LTACCmd>) =
            this.set(k, lastCmd)

        /**
         * joins all commands and key-value pairs from a [other] to [this]. If there is a discrepancy between the two values of
         * a key, the result is null.
         */
        infix fun Info?.joinWith(other: Info?): Info? {
            if (this == null || other == null) {
                return null
            }
            if (other.backing.any { (k, v) ->
                    k in backing && backing[k] != v
                }) {
                return null
            }
            return Info(
                backing = backing + other.backing,
                lastCmd = lastCmd.takeIf { it == other.lastCmd }
            )
        }
    }
}

inline operator fun <reified T> Info?.get(k: InfoKey<T>) =
    this?.let { getUntyped(k) as T? }

fun Info.lhs(k: InfoKey<LTACCmd>) =
    this[k]!!.cmd.getLhs()!!

