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
import analysis.CommandWithRequiredDecls.Companion.withDecls
import analysis.merge
import evm.EVM_WORD_SIZE
import tac.CallId
import tac.Tag
import vc.data.*
import java.math.BigInteger

class EVMInternalMemoryEncoder {
    fun allocate(bytesToAllocate: BigInteger, calleeIdx: CallId, write: WritableEVMInternalMemoryEncoder.() -> CommandWithRequiredDecls<TACCmd.Spec>): CommandWithRequiredDecls<TACCmd.Spec> {
        check(bytesToAllocate.mod(EVM_WORD_SIZE) == BigInteger.ZERO)
        val freePointer = TACKeyword.MEM64.toVar(calleeIdx)
        val start = TACKeyword.TMP(Tag.Bit256, "!offset").toUnique("!")
        val allocateRegion =
                listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(start, freePointer.asSym()),
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(freePointer,
                                TACExprFactTypeCheckedOnlyPrimitives.Add(
                                        freePointer.asSym(),
                                        bytesToAllocate.asTACSymbol().asSym()))).withDecls(
                        freePointer)
        val writes = WritableEVMInternalMemoryEncoder(start, BigInteger.ZERO, bytesToAllocate).write()
        return allocateRegion.merge(writes)
    }
}

class WritableEVMInternalMemoryEncoder private constructor(private val basePointer: TACSymbol.Var,
                                                           private val offsetBytes: BigInteger,
                                                           private val allocatedBytes: BigInteger,
                                                           private val commands: CommandWithRequiredDecls<TACCmd.Spec>) {

    constructor(basePointer: TACSymbol.Var, offsetBytes: BigInteger, allocatedBytes: BigInteger) :
            this(basePointer, offsetBytes, allocatedBytes, CommandWithRequiredDecls())

    fun writePrimitive(value: TACSymbol,
                       getBaseMap: (BigInteger) -> TACSymbol.Var,
                       cb: (CommandWithRequiredDecls<TACCmd.Spec>) -> CommandWithRequiredDecls<TACCmd.Spec>): WritableEVMInternalMemoryEncoder {
        check(offsetBytes < allocatedBytes) { "tried to write more bytes than were allocated" }
        val loc = TACKeyword.TMP(Tag.Bit256, "!loc").toUnique("!")
        val baseMap = getBaseMap(offsetBytes)
        val commands = listOf(
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                loc,
                TACExprFactTypeCheckedOnlyPrimitives.Add(
                    basePointer.asSym(),
                    offsetBytes.asTACSymbol().asSym())
            ),
            TACCmd.Simple.AssigningCmd.ByteStore(base = baseMap, loc = loc, value = value)
        ).withDecls(loc, basePointer, baseMap)
        return WritableEVMInternalMemoryEncoder(
                basePointer,
                offsetBytes + BigInteger.valueOf(32),
                allocatedBytes,
                this.commands.merge(cb(commands)))
    }

    fun close(): CommandWithRequiredDecls<TACCmd.Spec> {
        check(offsetBytes == allocatedBytes) { "did not use all allocated memory" }
        return commands
    }

}
