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

package spec.converters

import analysis.CommandWithRequiredDecls
import analysis.ip.InternalFuncValueLocation
import analysis.merge
import analysis.pta.abi.PartitionField
import datastructures.stdcollections.*
import evm.EVM_WORD_SIZE
import spec.CodeGenUtils
import spec.converters.repr.CVLDataInput
import spec.cvlast.typedescriptors.EVMTypeDescriptor
import spec.toProg
import tac.CallId
import tac.Tag
import utils.Either
import utils.toLeft
import utils.toRight
import utils.toValue
import vc.data.*
import vc.data.TACSymbol.Companion.atSync
import java.math.BigInteger

/**
 * Wrapper class representing a "location" into which a return value can be moved. Both implementations
 * wrap a simple [TACSymbol.Var]. The actual assignment to this wrapped variables depends on the specific subclass of [EVMInternalReturnData].
 */
sealed interface EVMInternalReturnData : EVMTypeDescriptor.EVMInternalSummaryReturn {
    companion object {
        operator fun invoke(v: TACSymbol.Var) : EVMInternalReturnData = EVMSymbolOutputReturn(v)
        operator fun invoke(v: TACSymbol.Var, fields: Map<PartitionField, InternalFuncValueLocation.PointerLayoutInfo>, callId: CallId) : EVMInternalReturnData = EVMReferenceTypeReturn(
            outSym = v.toLeft(),
            fields, callId
        )
        operator fun invoke(v : TACSymbol.Var, monolithicArray: TACSymbol.Var, callId: CallId) : EVMInternalReturnData = UnsplitEVMReturn(
            outSym = v.toLeft(),
            callId,
            monolithicArray
        )
    }
}

/**
 * Common class for moving primitive values.
 */
sealed interface EVMPrimitiveReturnData : EVMInternalReturnData {
    /**
     * Write a primitive value in [v] into the location represented by this class. [enc] describes how to encode the primitive type
     * into the evm representation via [spec.converters.EVMMoveSemantics.ValueConverters]
     */
    fun movePrimitiveValue(v: CVLDataInput, enc: Tag.CVLArray.UserArray.ElementEncoding) : CVLTACProgram
}

/**
 * Extension of [EVMInternalReturnData]
 */
sealed interface EVMReferenceReturnData : EVMInternalReturnData {
    /**
     * Assign a pointer [v] to the variable wrapped by this class. Not expected to be used directly, and is instead exposed for [allocateAndAssign].
     */
    fun movePointerValue(v: TACSymbol.Var) : CommandWithRequiredDecls<TACCmd.Spec>

    /**
     * Allocation an array of logical length [len], and then initialize the array with [cb]. The first argument of [cb], `loc` is a pointer
     * to the element data of the newly allocated array, and the second argument, `part`, is the memory map which holds that element data.
     *
     * The initialization code returned by [cb] is combined with the allocation code, and returned in a pair alongside a variable holding the newly allocated
     * object.
     */
    fun allocateArray(
        len: TACSymbol.Var,
        eSize: Int,
        cb: (loc: TACSymbol.Var, part: TACSymbol.Var, childGen: (TACSymbol.Var) -> EVMInternalReturnData) -> CVLTACProgram
    ) : Pair<TACSymbol.Var, CVLTACProgram>

    /**
     * Allocates a struct with [numFields], initializing its fields using [cb]. [cb] is called for each field, and is passed:
     * 1. the logical field number, 2. the raw offset within the struct, and 3. an [EVMInternalReturnData]
     * object which wraps the variable which will hold the initialized field value.
     *
     * [cb] is guaranteed to be called for each field, but no promises are made to the order (although it will be sequential for reasonable implementations).
     *
     * The allocation code, along with the field initialization and setting code are zipped together and returned alongside a variable which holds the newly allocated pointer.
     */
    fun allocateStruct(numFields: Int, cb: (Int, BigInteger, EVMInternalReturnData) -> CVLTACProgram) : Pair<TACSymbol.Var, CVLTACProgram>
}

/**
 * Allocate a fresh object using to the callback [cb] and the arguments [t] and [u]. [cb] is expected to be a function reference to either [EVMReferenceReturnData.allocateArray] or [EVMReferenceReturnData.allocateStruct].
 * In the former case, [t] is the symbol holding the array length and [u] is the element initialization callback. For the latter case, [t] is the number of fields (as a constant), and the field initialization callback.
 *
 * In either case, the pointer variable returned from these callbacks are assigned to [this] via [EVMReferenceReturnData.movePointerValue]
 */
fun <T, U> EVMReferenceReturnData.allocateAndAssign(cb: EVMReferenceReturnData.(T, U) -> Pair<TACSymbol.Var, CVLTACProgram>, t: T, u: U) : CVLTACProgram {
    val (ptr, gen) = this.cb(t, u)
    return gen.appendToSinks(this.movePointerValue(ptr))
}

/**
 * Allocate a fresh object using to the callback [cb] and the arguments [t] and [u]. [cb] is expected to be a function reference to either [EVMReferenceReturnData.allocateArray] or [EVMReferenceReturnData.allocateStruct].
 * In the former case, [t] is the symbol holding the array length and [u] is the element initialization callback. For the latter case, [t] is the number of fields (as a constant), and the field initialization callback.
 *
 * In either case, the pointer variable returned from these callbacks are assigned to [this] via [EVMReferenceReturnData.movePointerValue]
 */
fun <T, U, V> EVMReferenceReturnData.allocateAndAssign(cb: EVMReferenceReturnData.(T, U, V) -> Pair<TACSymbol.Var, CVLTACProgram>, t: T, u: U, v: V) : CVLTACProgram {
    val (ptr, gen) = this.cb(t, u, v)
    return gen.appendToSinks(this.movePointerValue(ptr))
}

/**
 * Private class to when the primitive value is a top-level return value.
 */
private class EVMSymbolOutputReturn(val outSym: TACSymbol.Var) : EVMPrimitiveReturnData {
    override fun movePrimitiveValue(v: CVLDataInput, enc: Tag.CVLArray.UserArray.ElementEncoding): CVLTACProgram {
        return v.readPrimitive { prim, ctxt ->
            EVMMoveSemantics.ValueConverters.convertValueTypeToEncoding(
                dest = outSym,
                src = prim,
                destEncoding = enc
            ).toProg("move", ctxt)
        }
    }
}

/**
 * Combination of [partition] (a [Tag.ByteMap] and offset within that partition [pointer] corresponding to a field pointer
 */
data class FieldPointer(val partition: TACSymbol.Var, val pointer: TACSymbol.Var)

/**
 * A wrapper for a primitive value that is stored in the EVM heap.
 *
 * Writes to the value are moved into the location indicated by [fld].
 */
private class EVMPrimitiveFieldReturn(val fld: FieldPointer) : EVMPrimitiveReturnData {
    override fun movePrimitiveValue(
        v: CVLDataInput,
        enc: Tag.CVLArray.UserArray.ElementEncoding
    ): CVLTACProgram {
        val output = TACKeyword.TMP(Tag.Bit256, "!toWrite").toUnique("!")
        return v.readPrimitive { prim, ctxt ->
            val conv = EVMMoveSemantics.ValueConverters.convertValueTypeToEncoding(
                dest = output,
                destEncoding = enc,
                src = prim
            )
            conv.merge(CommandWithRequiredDecls(listOf(TACCmd.Simple.AssigningCmd.ByteStore(
                base = fld.partition,
                loc = fld.pointer,
                value = output
                )), setOf(fld.partition, fld.pointer, output))
            ).toProg("move", ctxt)
        }
    }
}


/**
 * Indicating whether the output for a reference type should be placed into a top-level return variable,
 * or a field in another heap object.
 *
 * In principle we could have used this for the primitive case, but those classes are so small it seemed better to
 * just duplicate them.
 */
private typealias ReferenceTypeOutput = Either<TACSymbol.Var, FieldPointer>

/**
 * Common mixin type for handling allocating and initializing reference values. The type [T] is the piece of data which
 * represents field information, which bytemap to use for the field's data, and how to generate further [EVMInternalReturnData]
 * if that field itself is a reference type.
 */
sealed interface ReferenceReturnMixin<T> {
    /**
     * Get the type [T] that represents the location that data for [field] is stored. In partitioning mode, this is
     * the [InternalFuncValueLocation] object, in unsplit mode, this will simply be the monolithic memory arrays.
     */
    fun getPartition(
        field: PartitionField
    ) : T?

    /**
     * From the representation [T] of field's location, extract the actual bytemap variable which stores that data.
     */
    fun T.toPartitionVar(): TACSymbol.Var

    /**
     * Create an [EVMInternalReturnData] object for writing data into the field [fld], the pointer for which is
     * is in [pointerVar].
     */
    fun toReturnData(
        fld: T,
        pointerVar: TACSymbol.Var
    ) : EVMInternalReturnData

    val callId: CallId

    /**
     * Represents the output location of this reference type, either a variable on the stack (the left case)
     * or a field in some other object the [FieldPointer] object in the right case.
     */
    val outSym: Either<TACSymbol.Var, FieldPointer>

    fun allocateStructImpl(
        numFields: Int,
        cb: (Int, BigInteger, EVMInternalReturnData) -> CVLTACProgram
    ): Pair<TACSymbol.Var, CVLTACProgram> {
        /**
         * The output of the allocation, will hold the result of reading the free pointer
         */
        val newPointer = TACKeyword.TMP(Tag.Bit256, "!StructPointer").toUnique("!").atSync(callIndex = callId)

        /**
         * The free pointer (NB use of callId)
         */
        val fp = TACKeyword.MEM64.toVar(callId)
        /**
         * allocate and bump the free pointer, updating fp to be newPointer + numFields * 32 (aka EVM word size)
         */
        val alloc = CommandWithRequiredDecls(listOf(
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = newPointer,
                rhs = fp,
            ),
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = fp,
                rhs = TACExpr.Vec.Add(newPointer.asSym(), (numFields.toBigInteger() * EVM_WORD_SIZE).asTACExpr)
            )
        ), setOf(fp, newPointer))

        /**
         * All code for allocations
         */
        val allocCode = mutableListOf<CVLTACProgram>()
        /**
         * For each field
         */
        for(ind in 0 until numFields) {
            /**
             * Compute the partition information for where the field is held, and its offset w.r.t the base pointer
             */
            val fieldOffs = ind.toBigInteger() * EVM_WORD_SIZE
            val part = getPartition(PartitionField.StructField(fieldOffs)) ?: throw UnsupportedOperationException("Cannot find field output for $fieldOffs")

            /**
             * The pointer for the ind^th field
             */
            val fieldPointer = TACKeyword.TMP(Tag.Bit256, "!Field$ind!Pointer").toUnique("!").at(callId)
            val fieldComputation = CommandWithRequiredDecls(listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = fieldPointer,
                    rhs = TACExpr.Vec.Add(newPointer.asSym(), fieldOffs.asTACExpr)
                )
            ), setOf(newPointer, fieldPointer))
            /**
             * What type of field are we initializing? If its primitive vs reference, instantiate the appropriate
             * [EVMInternalReturnData] and invoke the callback.
             */
            val nextData = toReturnData(
                part,
                fieldPointer
            )

            val res = cb(ind, fieldOffs, nextData).prependToBlock0(fieldComputation)
            allocCode.add(res)
        }
        return newPointer to allocCode.reduce(::mergeCodes).prependToBlock0(alloc)
    }

    fun allocateArrayImpl(
        len: TACSymbol.Var,
        eSize: Int,
        cb: (loc: TACSymbol.Var, part: TACSymbol.Var, childGen: (TACSymbol.Var) -> EVMInternalReturnData) -> CVLTACProgram
    ): Pair<TACSymbol.Var, CVLTACProgram> {
        /**
         * The output of the allocation, we will read the free pointer and store it here
         */
        val newPointer = TACKeyword.TMP(Tag.Bit256, "!ArrayPointer").toUnique("!").atSync(callId)
        val fp = TACKeyword.MEM64.toVar(callId)
        val outPartition = getPartition(PartitionField.ArrayElement(eSize)) ?: throw UnsupportedOperationException("Cannot find array element information for $outSym")

        /**
         * Infer the element size of the output
         */
        val dataPart = outPartition.toPartitionVar()
        val lengthField = getPartition(PartitionField.ArrayLength)?.toPartitionVar()
            ?: throw UnsupportedOperationException("Cannot allocate array without array length field")

        /**
         * This is our pointer to the data segment, to be passed as the first argument to [cb]
         */
        val elementData = TACKeyword.TMP(Tag.Bit256, "!ElementData").toUnique("!")

        /**
         * As usual, word align the data size.
         */
        val (lenSym, lenData) = if(eSize == 1) {
            CodeGenUtils.wordAlignSymbol(len)
        } else {
            len to null
        }
        /**
         * All the code that effects the allocations.
         */
        val alloc = mutableListOf<CommandWithRequiredDecls<TACCmd.Spec>>()
        /**
         * Read the free pointer, assign it to newPointer (the freshly allocated object)
         */
        alloc.add(CommandWithRequiredDecls(listOf(
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = newPointer,
                rhs = fp
            )
        ), setOf(newPointer, fp)))
        /**
         * If we had to do size adjustments, add that here.
         */
        if(lenData != null) {
            alloc.add(lenData)
        }
        /**
         * Compute the size of the array block, and update the fp appropriately.
         * NB at this point, we don't care about TAC anymore, so we are generating complex expressions.
         */
        alloc.add(CommandWithRequiredDecls(listOf(
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = fp,
                rhs = TACExpr.Vec.Add(
                    newPointer.asSym(),
                    TACExpr.Vec.Add(
                        EVM_WORD_SIZE.asTACExpr,
                        TACExpr.Vec.Mul(
                            lenSym.asSym(),
                            eSize.asTACExpr
                        )
                    )
                )
            ),
            /**
             * Set the length (the location in memory pointed to by newPointer), using
             * the partition we read above
             */
            TACCmd.Simple.AssigningCmd.ByteStore(
                base = lengthField,
                loc = newPointer,
                value = len
            ),
            /**
             * Compute element data by adding 32 bytes to the new pointer, skipping over the length we just wrote
             */
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = elementData,
                rhs = TACExpr.Vec.Add(
                    EVM_WORD_SIZE.asTACExpr,
                    newPointer.asSym()
                )
            )
        ), setOf(len, fp, newPointer, lengthField, elementData, lenSym)))

        /**
         * Call back should initialize the primitive data
         */
        val initCode  =
            cb(elementData, dataPart) {
                toReturnData(
                    pointerVar = it,
                    fld = outPartition
                )
            }
        /**
         * And done, zip up all the code and return newPointer
         */
        return newPointer to initCode.prependToBlock0(CommandWithRequiredDecls.mergeMany(alloc))
    }

    /**
     * Depending on whether the [outSym] is a heap location or a variable, generate a simple expression move or byte store of
     * the value in [v].
     */
    fun movePointerValueImpl(v: TACSymbol.Var): CommandWithRequiredDecls<TACCmd.Spec> {
        return outSym.toValue({
            CommandWithRequiredDecls(
                listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = it,
                        rhs = v.asSym()
                    )
                ), setOf(v, it)
            )
        }, {
            CommandWithRequiredDecls(listOf<TACCmd.Spec>(
                TACCmd.Simple.AssigningCmd.ByteStore(
                    base = it.partition,
                    loc = it.pointer,
                    value = v
                )
            ), setOf(it.partition, it.pointer, v))
        })
    }

}

/**
 * The case used for when the memory space for an internal function is unsplit. This class is used
 * for writing both reference types and primitive types, as without the internal function value location, we can't
 * know a priori which type of return data to generate. This is a similar approach taken
 * with the unsplit argument data.
 */
private class UnsplitEVMReturn(
    override val outSym: ReferenceTypeOutput,
    override val callId: CallId,
    val monolithicArray: TACSymbol.Var
) : ReferenceReturnMixin<TACSymbol.Var>, EVMReferenceReturnData, EVMPrimitiveReturnData {
    override fun movePrimitiveValue(
        v: CVLDataInput,
        enc: Tag.CVLArray.UserArray.ElementEncoding
    ): CVLTACProgram {
        return v.readPrimitive { prim, ctxt ->
            outSym.toValue({
                EVMMoveSemantics.ValueConverters.convertValueTypeToEncoding(
                    dest = it,
                    src = prim,
                    destEncoding = enc
                ).toProg("Simple move", ctxt)
            }, {
                check(it.partition == monolithicArray)
                val tmp = TACKeyword.TMP(Tag.Bit256, "!toWrite").toUnique("!")
                EVMMoveSemantics.ValueConverters.convertValueTypeToEncoding(dest = tmp, src = prim, destEncoding = enc).merge(CommandWithRequiredDecls(listOf(
                    TACCmd.Simple.AssigningCmd.ByteStore(
                        base = monolithicArray,
                        loc = it.pointer,
                        value = tmp
                    )
                ), setOf(it.pointer, monolithicArray, tmp))).toProg("move", ctxt)
            })
        }
    }

    override fun movePointerValue(v: TACSymbol.Var): CommandWithRequiredDecls<TACCmd.Spec> {
        return movePointerValueImpl(v)
    }

    override fun allocateArray(
        len: TACSymbol.Var,
        eSize: Int,
        cb: (loc: TACSymbol.Var, part: TACSymbol.Var, childGen: (TACSymbol.Var) -> EVMInternalReturnData) -> CVLTACProgram
    ): Pair<TACSymbol.Var, CVLTACProgram> {
        return allocateArrayImpl(len, eSize, cb)
    }

    override fun allocateStruct(
        numFields: Int,
        cb: (Int, BigInteger, EVMInternalReturnData) -> CVLTACProgram
    ): Pair<TACSymbol.Var, CVLTACProgram> {
        return allocateStructImpl(numFields, cb)
    }

    override fun getPartition(field: PartitionField): TACSymbol.Var {
        return monolithicArray
    }

    override fun toReturnData(fld: TACSymbol.Var, pointerVar: TACSymbol.Var): EVMInternalReturnData {
        check(fld == monolithicArray)
        return UnsplitEVMReturn(
            callId = callId,
            monolithicArray = monolithicArray,
            outSym = FieldPointer(
                pointer = pointerVar,
                partition = monolithicArray
            ).toRight()
        )
    }

    override fun TACSymbol.Var.toPartitionVar(): TACSymbol.Var {
        return this
    }

}

/**
 * Wrapper around locations that need to be allocated and initialized.
 *
 * [outSym] indicates whether the result of the allocation should be placed in a variable or another heap location.
 * [fields] indicates how the [PartitionField]s for the abstract fields of the object are laid out in memory.
 * [callId] is used for selecting the correct version of the free pointer, and just for general coherence of temp variables.
 */
private class EVMReferenceTypeReturn(
    override val outSym: ReferenceTypeOutput,
    val fields: Map<PartitionField, InternalFuncValueLocation.PointerLayoutInfo>,
    override val callId: CallId
) : EVMReferenceReturnData, ReferenceReturnMixin<InternalFuncValueLocation.PointerLayoutInfo> {
    override fun allocateArray(
        len: TACSymbol.Var,
        eSize: Int,
        cb: (loc: TACSymbol.Var, part: TACSymbol.Var, childGen: (TACSymbol.Var) -> EVMInternalReturnData) -> CVLTACProgram
    ): Pair<TACSymbol.Var, CVLTACProgram> {
        return this.allocateArrayImpl(len, eSize, cb)
    }

    override fun allocateStruct(
        numFields: Int,
        cb: (Int, BigInteger, EVMInternalReturnData) -> CVLTACProgram
    ): Pair<TACSymbol.Var, CVLTACProgram> {
        return this.allocateStructImpl(numFields, cb)
    }

    /**
     * Depending on whether the [outSym] is a heap location or a variable, generate a simple expression move or byte store of
     * the value in [v].
     */
    override fun movePointerValue(v: TACSymbol.Var): CommandWithRequiredDecls<TACCmd.Spec> {
        return outSym.toValue({
            CommandWithRequiredDecls(
                listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = it,
                        rhs = v.asSym()
                    )
                ), setOf(v, it)
            )
        }, {
            CommandWithRequiredDecls(listOf<TACCmd.Spec>(
                TACCmd.Simple.AssigningCmd.ByteStore(
                    base = it.partition,
                    loc = it.pointer,
                    value = v
                )
            ), setOf(it.partition, it.pointer, v))
        })
    }

    override fun getPartition(field: PartitionField): InternalFuncValueLocation.PointerLayoutInfo? {
        return this.fields[field]
    }

    override fun toReturnData(
        fld: InternalFuncValueLocation.PointerLayoutInfo,
        pointerVar: TACSymbol.Var
    ): EVMInternalReturnData {
        return when (fld) {
            is InternalFuncValueLocation.PrimitiveField -> {
                EVMPrimitiveFieldReturn(
                    FieldPointer(
                        partition = fld.partitionVariable,
                        pointer = pointerVar
                    )
                )
            }

            is InternalFuncValueLocation.ReferenceField -> {
                /**
                 * In this case, we need to pass through the partition field information, and expose allocation operations
                 * via the type we pass in.
                 */
                EVMReferenceTypeReturn(
                    outSym = FieldPointer(
                        pointer = pointerVar,
                        partition = fld.partitionVariable
                    ).toRight(),
                    fields = fld.fields,
                    callId = callId
                )
            }
        }
    }

    override fun InternalFuncValueLocation.PointerLayoutInfo.toPartitionVar(): TACSymbol.Var {
        return this.partitionVariable
    }
}
