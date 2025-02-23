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

package analysis.controlflow

import analysis.bitvector.StaticBitVectorUniverse
import analysis.TACCommandGraph
import analysis.worklist.SimpleWorklist
import tac.NBId
import java.util.*

object MustPathInclusionAnalysis {
    /**
     * Compute for every pair of basic blocks a and b, the basic blocks that MUST occur on any path between a and b.
     *
     * Computed by iterating the following system of equations until it converges:
     *
     * f_0(a to b) = {a} (b is an immediate successor of b)
     * f_0(a to b) = {} (otherwise)
     *
     * f_i+1(a to b) = /\ s in succ(a),fi(s to b)
     */
    fun computePathInclusion(g: TACCommandGraph) : Map<Pair<NBId, NBId>, Set<NBId>> {
        val blocks = g.blocks
        val univ = StaticBitVectorUniverse(blocks.map { it.id })
        val predRelation = Array(blocks.size) { i ->
            val bs = BitSet(blocks.size)
            for(p in g.pred(blocks[i].id)) {
                bs.set(univ.lookup(p))
            }
            bs
        }

        val st = mutableMapOf<Long, BitSet>()
        g.scope {
            val seed = mutableListOf<Long>()
            for(block in g.blocks) {
                for(succ in block.id.succ()) {
                    val pair = inj(univ, block.id, succ)
                    val bs = BitSet(blocks.size)
                    bs.set(univ.lookup(block.id))
                    st[pair] = bs
                    seed.add(pair)
                }
            }

            val tmp = BitSet()
            SimpleWorklist.iterateWorklist(seed) { it, nxt ->
                tmp.clear()
                tmp.or(st[it]!!)
                val predSet = predRelation[it.first]
                var pred = predSet.nextSetBit(0)
                while(pred > -1) {
                    tmp.set(pred)
                    val k = inj(pred, it.second)
                    if(k !in st) {
                        st[k] = tmp.clone() as BitSet
                        nxt.add(k)
                        continue
                    }
                    val predPathSet = st[k]!!
                    var changed = false
                    var nextSetInPred = predPathSet.nextSetBit(0)
                    while(nextSetInPred > -1) {
                        if(!tmp.get(nextSetInPred)) {
                            changed = true
                            predPathSet.clear(nextSetInPred)
                        }
                        nextSetInPred = predPathSet.nextSetBit(nextSetInPred + 1)
                    }
                    if(changed) {
                        nxt.add(k)
                    }
                    tmp.clear(pred)
                    pred = predSet.nextSetBit(pred + 1)
                }
            }
        }
        val toRet = mutableMapOf<Pair<NBId, NBId>, Set<NBId>>()
        for((k, v) in st) {
            val start = univ.lookup(k.first)
            val end = univ.lookup(k.second)
            val s = mutableSetOf<NBId>()
            for (i in v.stream()) {
                s.add(univ.lookup(i))
            }
            toRet[start to end] = s
        }
        return toRet
    }

    private val Long.first: Int get() = this.shr(32).toInt()

    private val Long.second: Int get() = this.toInt()

    private fun inj(universe: StaticBitVectorUniverse<NBId>, id: NBId, succ: NBId): Long {
        val fst = universe.lookup(id)
        val snd = universe.lookup(succ)
        return inj(fst, snd)
    }

    private fun inj(fst: Int, snd: Int) = (fst.toLong() shl 32) or (snd.toLong())


}