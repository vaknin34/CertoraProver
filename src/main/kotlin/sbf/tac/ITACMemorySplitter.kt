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

package sbf.tac

import sbf.cfg.LocatedSbfInstruction
import sbf.disassembler.SbfRegister
import sbf.domains.MemSummaryArgumentType
import sbf.domains.PTAOffset

/**
 * Disambiguate a memory access by mapping the memory access to a symbolic variable
 **/
interface TACMemSplitter {
    /**
     *  @param locInst is a memory instruction (store or load)
     *  @return  a (symbolic) TAC variable that represents the memory location being de-referenced.
     *  If inst is not reachable then it returns null.
     **/
    fun getTACMemory(locInst: LocatedSbfInstruction): LoadOrStoreInfo?

    /**
     *  @param locInst is a call to `sol_memcpy_`, `sol_memmove_`, `sol_memcmp_`, or `sol_memset_`
     *  @return all TAC variables that represent the source and destination memory locations.
     *  If inst is not reachable then it returns null.
     */
    fun getTACMemoryFromMemIntrinsic(locInst: LocatedSbfInstruction): MemInstInfo?

    /**
     * @param locInst is call to an internal function.
     * @return a list of memory locations that are modified by the summary.
     * If inst is not reachable then it returns null.
     */
    fun getTACMemoryFromSummary(locInst: LocatedSbfInstruction): List<SummaryArgInfo>?


    /** class to model in TAC memory load and store instructions
     *  @param variable: TAC variable that models the de-referenced memory location. It can be a scalar or a byteMap
     *  @param locationsToHavoc is the list of scalars or byte map indexes to be havoc
     **/
    data class LoadOrStoreInfo(val variable: TACVariable,
                               val locationsToHavoc: HavocMemLocations)

    /**
     * class to model that (*[reg]+[offset]) is mapped to [variable] and has type [type]
     */
    data class SummaryArgInfo(val reg: SbfRegister, val offset: Long, val width: Byte, val allocatedSpace: ULong,
                              val type: MemSummaryArgumentType, val variable: TACVariable)
    /**
     * class to model in TAC memory instructions: `sol_memcpy_`, `sol_memmove_`, `sol_memcmp_`, or `sol_memset_`
     * Currently, we only model sol_memcpy_ and sol_memcmp_.
     **/
    sealed class MemInstInfo
    /** class to model sol_memcpy **/
    sealed class MemTransferInfo: MemInstInfo()
    /** class to model sol_memcmp **/
    sealed class MemCmpInfo: MemInstInfo()
    /** class to model sol_memset **/
    sealed class MemsetInfo: MemInstInfo()
    /** class to model sol_memmove and sol_memset which are not supported at the moment **/
    object NotImplMemInstInfo : MemInstInfo()


    /** class to keep track which TAC variables should be havoc **/
    sealed class HavocMemLocations
    data class HavocScalars(val vars: List<TACByteStackVariable>): HavocMemLocations()
    data class HavocMapBytes(val fields: List<PTAOffset>): HavocMemLocations()

    /**
     *  Transfer memory from stack to stack
     *
     *  @property sourceRange is a pair of lowest and highest offsets being copied from the stack.
     *  @property destinationRange is a pair of lowest and highest offsets being copied to the stack.
     *  @property length is the number of bytes being copied.
     **/
    class StackMemTransferInfo(
        val sourceRange: Pair<Long, Long>,
        val destinationRange: Pair<Long, Long>,
        val length: Long,
        val locationsToHavoc: HavocScalars): MemTransferInfo()

    /**
     * Transfer memory from non-stack to non-stack
     **/
    class NonStackMemTransferInfo(
        val source: TACByteMapVariable,
        val destination: TACByteMapVariable,
        val length: Long?,
        val locationsToHavoc: HavocMapBytes): MemTransferInfo()

    /**
     * Transfer memory from non-stack to stack, or vice-versa.
     */
    class MixedRegionsMemTransferInfo (
        val byteMap: TACByteMapVariable,
        val stackOpRange: Pair<Long, Long>,
        /// To know the direction of the transfer. If true then from non-stack to stack
        val isDestStack: Boolean,
        val length: Long,
        val locationsToHavoc: HavocMemLocations
    ): MemTransferInfo() {
        init {
            if (isDestStack) {
                check(locationsToHavoc is HavocScalars) {"precondition of MixedRegionsMemTransferInfo failed (1)"}
            } else {
                check(locationsToHavoc is HavocMapBytes) {"precondition of MixedRegionsMemTransferInfo failed (2)"}
            }
        }
    }

    /** Class to represent sol_memcpy instructions that cannot be translated to TAC **/
    object UnsupportedMemTransferInfo: MemTransferInfo()


    /**
     * This is a wrapper that conveniently groups together `sol_memcmp_` operands as TAC variables.
     * Both memcmp operands point to the stack.
     *
     *  @property op1 is a list of destination TAC variables.
     *  @property op2 is a list of source TAC variables.
     *  @property op1Range is a pair of lowest and highest offsets being compared on the stack.
     *  @property op2Range is a pair of lowest and highest offsets being compared on the stack.
     *  @property length is the number of bytes to be compared.
     *  @property wordSize is the size of a word in bytes.
     *
     *  The number of words is [length]/[wordSize].
     */
    class StackMemCmpInfo (
        val op1: List<TACByteStackVariable>,
        val op2: List<TACByteStackVariable>,
        val op1Range: Pair<Long, Long>,  // for generating TAC metadata
        val op2Range: Pair<Long, Long>,  // for generating TAC metadata
        val length: Long,
        val wordSize: Byte
    ): MemCmpInfo()  {
        init {
            // source and destination must have the same number of variables
            if (op1.size != op2.size) {
                throw TACTranslationError("creating an invalid StackMemCmpInfo object")
            }
        }
    }

    /**
     * This is a wrapper that conveniently groups together `sol_memcmp_` operands as TAC variables.
     * Both memcmp operands point to non-stack memory.
     *
     *  @property length is the number of bytes to be compared.
     *  @property wordSize is the size of a word in bytes.
     *
     *  The number of words is [length]/[wordSize].
     */
    class NonStackMemCmpInfo (
        val op1: TACByteMapVariable,
        val op2: TACByteMapVariable,
        val length: Long,
        val wordSize: Byte
    ): MemCmpInfo()

    /**
     *  One memcmp operand is on the stack but the other is not.
     *
     *  Operands are normalized so that [scalars] is always a list of scalars and [byteMap] is a byte map.
     *  [scalarsReg] ([byteMapReg]) tells which register (r1 or r2) is [scalars] ([byteMap]).
     */
    class MixedRegionsMemCmpInfo (
        val scalars: List<TACByteStackVariable>,
        val byteMap: TACByteMapVariable,
        val scalarsReg: SbfRegister,
        val byteMapReg: SbfRegister,
        val stackOpRange: Pair<Long, Long>?,  // for generating TAC metadata
        val length: Long,
        val wordSize: Byte
    ): MemCmpInfo()  {
        init {
            if (scalarsReg == byteMapReg) {
                throw TACTranslationError("creating an invalid MixedRegionsTACMemCmpInfo object (1)")
            }
            if (!(scalarsReg >= SbfRegister.R1_ARG && scalarsReg <= SbfRegister.R2_ARG) ) {
                throw TACTranslationError("creating an invalid MixedRegionsTACMemCmpInfo object (2)")
            }
            if (!(byteMapReg >= SbfRegister.R1_ARG && byteMapReg <= SbfRegister.R2_ARG) ) {
                throw TACTranslationError("creating an invalid MixedRegionsTACMemCmpInfo object (3)")
            }
        }
    }

    /** Class to represent sol_memcmp instructions that cannot be translated to TAC **/
    object UnsupportedMemCmpInfo: MemCmpInfo()

    /** Class to represent a memset on the stack **/
    class StackZeroMemsetInfo(val stackOpRange: Pair<Long, Long>, val length: Long): MemsetInfo()

    /** Class to represent a memset on a non-stack memory region **/
    class NonStackMemsetInfo(val byteMap: TACByteMapVariable, val value: Long, val length: Long): MemsetInfo()

    /** Class to represent memset instructions that cannot be translated to TAC **/
    object UnsupportedMemsetInfo: MemsetInfo()
}


