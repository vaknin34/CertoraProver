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

package analysis.worklist

import datastructures.stdcollections.*

object SimpleWorklist {

    /**
     * A function for processing a collection of work items that the processing lambda can expand as it process each item;
     * the lambda processing function may also shut down work item processing with an early exit continuation.
     *
     * iterateWorklist starts with a collection of work items. It iterates through the work items, processing each
     * work item by _processor_. For each pass through the collection of work items, the _processor_ lambda receives a
     * mutable set of work items as an argument that the lambda function can use for adding new work items for processing.
     * After the function finishes the initial work set, the function will then iterate through any new work items added
     * by the processing function. The lambda function has a special third argument, a lambda that represents an exit
     * continuation. The _processor_ lambda can call the exit lambda at any time with a return value of type R. R may
     * not be null. When the _processor_ lambda invokes the exit function, iterateWorklist will return the value given
     * to the exit continuation and not process any more work items in the collection.
     *
     * @param[T] the type of the work items
     * @param[R] the type of object returned from the work item processing.
     * @param[seed] the starting collection of work items.
     * @param[processor] the lambda function invoked for each work item.
     * @param[item] the next item on which to work.
     * @param[nextItems] the mutable collection in which to add more things on which to work.
     * @param[exitContinuation] the continuation to call to end the work list. Pass the
     * work list exit value in [exitValue]
     * @param[exitValue] the value to give to [exitContinuation] as the return value of the
     * work list.
     */
    fun <T, R : Any> iterateWorklist(
        seed: Collection<T>,
        processor: (item: T, nextItems: MutableCollection<T>, exitContinuation: (exitValue: R) -> Unit) -> Unit
    ): R? {
        var worklist = seed.toMutableSet()
        var next = mutableSetOf<T>()
        while(worklist.isNotEmpty()) {
            var thing: R? = null
            for(it in worklist) {
                processor(it, next) {
                    thing = it
                }
                if (thing != null) {
                    return thing
                }
            }
            val tmp = worklist
            worklist = next
            next = tmp
            next.clear()
        }
        return null
    }

    /**
     * A function for processing a collection of work items that the processing lambda can expand as it process each item.
     *
     * iterateWorklist starts with a collection of work items. It iterates through the work items, processing each
     * work item by _processor_. For each pass through the collection of work items, the _processor_ lambda receives a
     * mutable set of work items as an argument that the lambda function can use for adding new work items for processing.
     * After the function finishes the initial work set, the function will then iterate through any new work items added
     * by the processing function. Processing of work items continues util the processor function adds no more work
     * items.
     *
     * @param[seed] the starting collection of work items.
     * @param[processor] the lambda function invoked for each work item.
     * @param[item] the next item on which to work.
     * @param[nextItems] the mutable collection in which to add more things on which to work.
     */
    fun <T> iterateWorklist(seed: Collection<T>, processor: (item: T, nextItems: MutableCollection<T>) -> Unit) {
        iterateWorklist<T, Unit>(seed) {
            // For this use of iterateWorklist with the exit continuation, we actually never call the exit continuation.
            thing, mutableCollection, _ ->
            processor(thing, mutableCollection)
        }
    }
}
