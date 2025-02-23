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

package analysis

import com.certora.collect.*
import datastructures.stdcollections.*
import log.Logger
import log.LoggerTypes
import vc.data.EVMTACProgram
import vc.data.MutableBlockGraph

private val logger = Logger(LoggerTypes.COMMON)

fun removeEmptyBlocks(code: EVMTACProgram) : EVMTACProgram {
    // TODO: The bug here is that need to run until no empty blocks exist
    val newCode = code.code.toMutableMap()
    val newGraph = MutableBlockGraph(code.blockgraph)
    code.code.forEach { bAndCode ->
        if (bAndCode.value.isEmpty()) {
            val preds = newGraph.filter { bAndCode.key in it.value }.keys
            val succs = newGraph[bAndCode.key]!!

            preds.forEach { pred ->
                val origSucc = newGraph[pred]!!
                logger.info { "When removing ${bAndCode.key}, linking its predecessor $pred to $origSucc minus the removed plus $succs"}
                newGraph.put(pred, origSucc.minus(bAndCode.key).plus(succs))
            }

            logger.info { "Removing ${bAndCode.key} which is empty, linked $preds to $succs"}
            newCode.remove(bAndCode.key)
            newGraph.remove(bAndCode.key)
        }
    }

    return code.copy(newCode,newGraph)
}

