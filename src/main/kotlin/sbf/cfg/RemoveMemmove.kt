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

package sbf.cfg

/**
 *  Replace memmove with memcpy instructions
 **/
fun removeMemmove(cfg: MutableSbfCFG) {
    for (b in cfg.getMutableBlocks().values) {
        for (locInst in b.getLocatedInstructions()) {
            val inst = locInst.inst
            if (inst is SbfInstruction.Call && inst.name == "sol_memmove_") {
                // Replace in-place the instruction with memcpy
                val newMetaData = inst.metaData.plus(Pair(SbfMeta.REMOVED_MEMMOVE, ""))
                val newMemcpyInst = inst.copy(name="sol_memcpy_", metaData = newMetaData)
                b.replaceInstruction(locInst, newMemcpyInst)
            }
        }
    }
}

