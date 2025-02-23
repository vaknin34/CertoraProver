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

import sbf.SolanaConfig
import sbf.disassembler.SbfConstantStringGlobalVariable
import sbf.disassembler.SbfGlobalVariable
import sbf.disassembler.GlobalVariableMap
import sbf.domains.Constant

/**
 * A SBF (Solana Binary Format) program has access to these four pairwise disjoint regions:
 * - Input (aka "Context" in Linux eBPF): solana accounts
 * - Stack frame: fixed-size, byte-addressable array of 4 KB
 * - Heap: a byte-addressable region for dynamic memory designated between [0x300000000, 0x3000077f8]
 * - Global: global variables (e.g., constant strings)
 *
 * A pointer is a pair of a memory region (input, stack, heap or global) and an offset
 *
 * A SBF program has also access to 11 registers: r0, r1, ..., r10.
 * A register can store either a number or a pointer to any of the above memory regions.
 * Initially, r10 points to the end of the stack.
 * The register r10 is read-only.
 *
 * More concretely, the type of a register is defined by this finite lattice:
 *
 *             ----------------- Top
 *           /                    |
 *          /         -------- Pointer ---------
 *        /         /          |         |      \
 *      Num       Stack     Input    Heap   Global
 *        \            \      |        /       /
 *          -------------- Bottom -------------
 *  where
 *  - Top: any type
 *  - Bottom: type error
 *  - Num: number
 *  - Stack: pointer to the stack (i.e., it contains a stack offset)
 *  - Input: pointer to the input region
 *  - Heap: pointer to the heap (i.e, an integer between [0x300000000, 0x3000077f8])
 *  - Global: pointer to a global variable
 *
 *  In SBF, numbers and pointers are indistinguishable so there are implicit casts
 *  from numbers to pointers, and vice-versa.
 **/

const val SOLANA_ACCOUNT_SIZE = 10 * 1024 * 1024
const val MAX_SOLANA_ACCOUNTS = 50

const val NUM_OF_SBF_REGISTERS = 11

// -- Actual SVM parameters
// In SVM, each memory region must be 1 << 32 bytes apart, where 32 is the number of bits of a virtual address.
// The code region includes the bytecode and the .rodata section
const val SBF_CODE_START = 0x100_000_000
val SBF_STACK_FRAME_SIZE = SolanaConfig.StackFrameSize.get().toLong()
const val SBF_STACK_START = 0x200_000_000
const val SBF_INPUT_START = 0x400_000_000
const val SBF_HEAP_SIZE = 32_768
const val SBF_HEAP_START = 0x300_000_000

// -- Parameters needed for TAC encoding
const val SBF_HEAP_END = SBF_HEAP_START + SBF_HEAP_SIZE
// In SVM, there is no explicit limit for the input area, but probably, it's the last addressable virtual address.
// For TAC encoding purposes, we need to choose an end. We don't really care the exact value.
const val SBF_INPUT_END = SBF_INPUT_START + (2 * MAX_SOLANA_ACCOUNTS * SOLANA_ACCOUNT_SIZE)
// This is not an actual SVM memory region, but we needed for TAC encoding purposes.
// We have split the input memory region into two parts: the first half for solana accounts and the second half for external allocations.
const val SBF_EXTERNAL_START = SBF_INPUT_START + (MAX_SOLANA_ACCOUNTS * SOLANA_ACCOUNT_SIZE)

typealias ConstantNum = Constant
typealias ConstantOffset = Constant

sealed class SbfType {
    // To represent type errors
    object Bottom : SbfType() {
        override fun toString(): String {
            return "bottom"
        }
    }

    // Any type
    object Top : SbfType() {
        override fun toString(): String {
            return "top"
        }

    }

    // Numerical type
    data class NumType(val value: ConstantNum): SbfType() {
        override fun toString(): String {
            return if (value.isTop()) {
                "num"
            } else {
                "num($value)"
            }
        }
    }

    // Pointer type
    sealed class PointerType: SbfType() {
        abstract val offset : ConstantOffset
        abstract fun withOffset(newOffset: ConstantOffset): PointerType

        data class Stack(override val offset: ConstantOffset): PointerType() {
            override fun toString(): String {
                return "sp($offset)"
            }
            override fun withOffset(newOffset: ConstantOffset) = Stack(newOffset)

        }

        data class Input(override val offset: ConstantOffset): PointerType() {
            override fun toString(): String {
                return "input($offset)"
            }
            override fun withOffset(newOffset: ConstantOffset) = Input(newOffset)
        }

        data class Heap(override val offset: ConstantOffset): PointerType() {
            override fun toString(): String {
                return "heap($offset)"
            }
            override fun withOffset(newOffset: ConstantOffset) = Heap(newOffset)
        }

        // global.address is the start address of the global variable.
        // offset is actually an absolute address between [global.address, global.address+size)
        data class Global(override val offset: ConstantOffset,
                          val global: SbfGlobalVariable?): PointerType() {
            override fun toString(): String {
                return if (global != null) {
                    if (global is SbfConstantStringGlobalVariable) {
                        "global($global)"
                    } else {
                        "global(${global.name}, $offset)"
                    }
                } else {
                    "global($offset)"
                }
            }
            override fun withOffset(newOffset: ConstantOffset) = Global(newOffset, global)
        }
    }

    fun join(other: SbfType): SbfType {
        if (this is Bottom) {
            return other
        } else if (other is Bottom) {
            return this
        } else if (this is Top || other is Top) {
            return Top
        }

        return if (this is NumType && other is NumType) {
            NumType(value.join(other.value))
        } else if (this is PointerType.Stack && other is PointerType.Stack) {
            PointerType.Stack(offset.join(other.offset))
        } else if (this is PointerType.Input && other is PointerType.Input) {
            PointerType.Input(offset.join(other.offset))
        } else if (this is PointerType.Heap && other is PointerType.Heap) {
            PointerType.Heap(offset.join(other.offset))
        } else if (this is PointerType.Global && other is PointerType.Global) {
            PointerType.Global(offset.join(other.offset),
                                if (global == other.global) {
                                    global
                                } else {
                                    null
                                })
        } else {
            Top
        }
    }

    fun lessOrEqual(other: SbfType): Boolean {
        if (other is Top || this is Bottom) {
            return true
        } else if (this is Top || other is Bottom) {
            return false
        }

        return if (this is NumType && other is NumType) {
            value.lessOrEqual(other.value)
        } else if (this is PointerType.Stack && other is PointerType.Stack) {
            offset.lessOrEqual(other.offset)
        } else if (this is PointerType.Input && other is PointerType.Input) {
            offset.lessOrEqual(other.offset)
        } else if (this is PointerType.Heap && other is PointerType.Heap) {
            offset.lessOrEqual(other.offset)
        } else if (this is PointerType.Global && other is PointerType.Global) {
            offset.lessOrEqual(other.offset)
        } else {
            false
        }
    }
}

fun samePointerType(t1: SbfType.PointerType, t2: SbfType.PointerType) = t1::class == t2::class

/**
 *  Cast a number type to a pointer type
 *
 *  We cast a number only if the number is a valid heap address or the address of a global variable.
 *  We don't try to cast a number to a pointer if the number can be a valid address in the stack or input regions.
 *  In that case, we will return null.
 * **/
fun castNumToPtr(src: SbfType.NumType, globalsMap: GlobalVariableMap): SbfType.PointerType? {
    fun findLowerBound(key: Long): Pair<Long, SbfGlobalVariable>? {
        // globalsMap is sorted
        var lb: Pair<Long, SbfGlobalVariable> ? = null
        for (kv in globalsMap) {
            if (kv.key <= key) {
                lb = Pair(kv.key, kv.value)
            } else {
                break
            }
        }
        return lb
    }

    val n = src.value.get()
    if (n != null) {
        if (n in SBF_HEAP_START until SBF_HEAP_END) {
            val offset = ConstantOffset(n).sub(ConstantOffset(SBF_HEAP_START))
            check(!offset.assume(CondOp.SLT, Constant(0L)).isTrue())
            {"Offsets of pointers to the Heap region heap cannot be negative"}
            return SbfType.PointerType.Heap(offset)
        } else {
            // We check if n can be a valid address assigned to a global variable.
            val lb = findLowerBound(n)
            if (lb != null) {
                val globalVar = lb.second
                if (globalVar.size == 0L) {
                    // The global might have been inferred by GlobalInferenceAnalysis.
                    // We assume that offset is the start of the global
                    val offset = ConstantOffset(n)
                    return SbfType.PointerType.Global(offset, globalVar)
                }
                else if (n >= globalVar.address && (n < (globalVar.address + globalVar.size))) {
                    // Note that in case of an array, `offset` might not be the start address of the global.
                    // That is, it's not always true that offset == globalVar.address
                    val offset = ConstantOffset(n)
                    return SbfType.PointerType.Global(offset, globalVar)
                }
            }
        }
    }
    /// We are here if the number cannot be either the address of a global or a valid address
    /// in the heap.
    return null
}
