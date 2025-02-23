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

package rules.dpgraph

import java.util.concurrent.atomic.AtomicInteger


/**
 * An ordinal associated to [DPGraph]'s nodes to validate that task execution is done in a topological order.
 */
interface ExecutionOrdinal<T : Comparable<T>>: Comparable<ExecutionOrdinal<T>> {
    val ord: T
    override fun equals(other: Any?): Boolean
    override fun hashCode(): Int
}

/**
 * An ordinal associated to a computation carried in [DPGraphTraversal].
 */
@JvmInline
value class ExecutionIntOrdinal(override val ord: Int) : ExecutionOrdinal<Int> {
    override fun compareTo(other: ExecutionOrdinal<Int>): Int = ord.compareTo(other.ord)
}

/**
 * Generates an [ExecutionOrdinal] of type [T].
 */
interface ExecutionOrdinalFactory<T: Comparable<T>> {

    /**
     * A minimal ordinal with respect to [T]'s order relation.
     */
    val bottom: ExecutionOrdinal<T>

    /**
     * Generates the next ordinal, should be greater than the last generated ordinal.
     */
    fun next(): ExecutionOrdinal<T>
}

/**
 * Non-negative integer valued ordinal. Ordinal generation is thread safe.
 */
class ExecutionIntOrdinalFactory : ExecutionOrdinalFactory<Int> {
    override val bottom = ExecutionIntOrdinal(0)
    private val taskNum = AtomicInteger(0)

    /**
     * Thread safe implementation of [ExecutionOrdinalFactory.next].
     */
    override fun next() : ExecutionIntOrdinal = ExecutionIntOrdinal(taskNum.addAndGet(1))
}
