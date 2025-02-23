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

package sbf.disassembler

import sbf.cfg.SbfInstruction
import com.certora.collect.*

sealed class Label {
    /** @return a fresh label derived from this label */
    abstract fun refresh(): Label

    /** A label corresponding to an original program address */
    data class Address(val address: Long): Label() {
        override fun refresh(): Label {
            return Refresh(address, allocFresh())
        }
        override fun toString() = "$address"
    }

    /** A label derived from an original program label */
    private data class Refresh(val address: Long, val fresh: Long): Label() {
        override fun refresh(): Label {
            return this.copy(fresh = allocFresh())
        }
        override fun toString() = "${address}_${fresh}"
    }

    /** An invented program label */
    private data class Fresh(val fresh: Long): Label() {
        override fun refresh(): Label {
            return this.copy(fresh = allocFresh())
        }
        override fun toString() = "fresh_${fresh}"
    }

    companion object {
        private var ctr: Long = 0L

        private fun allocFresh(): Long = ctr++

        /** Create a new fresh label */
        fun fresh(): Label {
            return Fresh(allocFresh())
        }
    }
}

typealias SbfLabeledInstruction = Pair<Label, SbfInstruction>

/**
 *  Representation of an arbitrary global variable.
 *  [size] can be 0 if unknown (this is possible if the global variable is not part of the ELF symbol table)
 **/
open class SbfGlobalVariable(val name: String, val address: ElfAddress, val size: Long)
/**
 *  Representation of a constant numerical global variable.
 *  The global variable is read-only and [value] contains its constant value.
 **/
data class SbfConstantNumGlobalVariable(private val _name:String, private val _address: ElfAddress, private val _size: Long, val value: Long)
    : SbfGlobalVariable(_name, _address, _size)
/**
 *  Representation of a constant string global variable.
 *  The global variable is read-only and [value] contains its constant value.
 **/
data class SbfConstantStringGlobalVariable(private val _name:String, private val _address: ElfAddress, private val _size: Long, val value: String)
    : SbfGlobalVariable(_name, _address, _size) {
        override fun toString() = value
    }

typealias GlobalVariableMap = TreapMap<ElfAddress, SbfGlobalVariable>
fun newGlobalVariableMap(): GlobalVariableMap = treapMapOf()
fun newGlobalVariableMap(vararg pairs: Pair<ElfAddress, SbfGlobalVariable>) = treapMapOf(*pairs)

/**
 * A SBF program is a sequence of SBF instructions, not yet a CFG.
 **/
data class SbfProgram(val entriesMap: Map<String, ElfAddress>, val funcMan: SbfFunctionManager,
                       val globalsMap: GlobalVariableMap,
                       val program: List<SbfLabeledInstruction>) {
    override fun toString(): String {
        val strBuilder = StringBuilder()
        for (inst in program) {
            strBuilder.append("${inst.first}: ${inst.second}\n")
        }
        return strBuilder.toString()
    }
}
