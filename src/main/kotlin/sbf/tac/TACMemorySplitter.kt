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

import sbf.*
import sbf.analysis.IRegisterTypes
import sbf.cfg.*
import sbf.disassembler.*
import sbf.domains.*
import sbf.analysis.MemoryAnalysis
import sbf.callgraph.SolanaFunction
import tac.Tag
import vc.data.TACSymbol
import datastructures.stdcollections.*

/**
 *  Dummy class in case no memory splitting is done.
 *  All pointers are mapped to the same variable
 **/
class DummyMemSplitter(// State for the TAC translation
    declaredVars: ArrayList<TACSymbol.Var>,
    private val regTypes: IRegisterTypes): TACMemSplitter {
    private val mem: TACVariable = TACByteMapVariable(TACSymbol.Var("UntypedMem", Tag.ByteMap))
    init { declaredVars.add(mem.tacVar) }

    override fun getTACMemory(locInst: LocatedSbfInstruction) =
        TACMemSplitter.LoadOrStoreInfo(mem, TACMemSplitter.HavocScalars(listOf()))
    override fun getTACMemoryFromSummary(locInst: LocatedSbfInstruction) =
        listOf<TACMemSplitter.SummaryArgInfo>()
    override fun getTACMemoryFromMemIntrinsic(locInst: LocatedSbfInstruction): TACMemSplitter.MemInstInfo  {
        val inst = locInst.inst
        check(inst is SbfInstruction.Call)
        return when (SolanaFunction.from(inst.name)) {
            SolanaFunction.SOL_MEMCPY -> {
                TACMemSplitter.NonStackMemTransferInfo(mem as TACByteMapVariable, mem, null,
                                                        TACMemSplitter.HavocMapBytes(listOf()))
            }
            SolanaFunction.SOL_MEMCMP -> {
                val lenType = regTypes.typeAtInstruction(locInst, SbfRegister.R3_ARG)
                if (lenType is SbfType.NumType) {
                    val len = lenType.value.get()
                    if (len != null) {
                        TACMemSplitter.NonStackMemCmpInfo(mem as TACByteMapVariable, mem, len, SolanaConfig.WordSize.get().toByte())
                    } else {
                        TACMemSplitter.UnsupportedMemCmpInfo
                    }
                } else {
                    TACMemSplitter.UnsupportedMemCmpInfo
                }
            }
            SolanaFunction.SOL_MEMSET -> {
                TACMemSplitter.UnsupportedMemsetInfo
            }
            else -> {
               TACMemSplitter.NotImplMemInstInfo
            }
        }
    }
}

/**
 * Perform memory splitting (aka memory disambiguation) by leveraging the Memory domain
 *
 *  For a given memory load or store at location l, we get the PTACell c being de-referenced.
 *  - If c points to the stack at l, then c is modeled as a scalar variable.
 *  - Otherwise, c is modeled as a ByteMap variable.
 *
 *  Recall that the stack is modeled in a flow-sensitive way: each location has its own stack.
 *  During the mapping from a cell to a scalar, the same stack offset is mapped to the same scalar variable
 *  regardless to which stack the cell points to. Thus, this can be seen as a flow-insensitive encoding of the stacks.
 *
 *  For solana memory instructions (sol_memcpy, sol_memmove, sol_memset, and sol_memcmp) we only support
 *  sol_memcpy and sol_memcmp.
 *
 *  The encoding of sol_memcpy differs whether source and destination cells are modeled as scalars or a single ByteMap.
 *  If both source and destination are ByteMap then we can use directly TAC ByteLongCopy.
 *  If both source and destination are scalars then we need to generate a sequence of assignments between
 *  scalar variables. Under some conditions, we allow to mix scalars and ByteMap (when copying from/to heap to stack).
 *  The scalar encoding of sol_memcpy only generates assignments if the destination
 *  cell is used in the program. If the destination cell is used in the program but the source cell is not
 *  (e.g., it is used outside the program under verification) then the destination cell is havocked.
 *
 *  The encoding of sol_memcmp is done differently. Similar to sol_memcpy, source and destination cells can be modeled
 *  either as scalars or a single ByteMap. Unlike sol_memcpy, the encoding of sol_memcmp is not done based on "use"
 *  because even if source or destination is not used in the program, we want to model them because otherwise we might
 *  miss equalities. For instance,
 *  ```
 *    b1:= sol_memcmp(x, z, 32)
 *    b2:= sol_memcmp(y, z, 32)
 *    if (b1==0 && b2==0) { ... }
 *  ```
 *  Even if z is not used in the program, we can infer that x and y are equal inside the "then" branch.
 *  Thus, for sol_memcmp we split the range of bytes to be compared in words and add equalities between each pair of
 *  source-destination words regardless whether the corresponding cells are used in the program.
 *  To do this, we need to fix a priori the word size, but we check with the Memory domain
 *  that the program is consistent with the selected word size. That is, all the accesses in the program for source and
 *  destination locations always access a number of bytes equal to the word size.
 *  If not, the precise encoding of sol_memcmp cannot be done, and we resort to the imprecise one.
 **/

class PTAMemSplitter(private val cfg: SbfCFG,
                     private val vFac: TACVariableFactory,
                      // Memory analysis
                     private val analysis: MemoryAnalysis,
                      // Global state needed to reply invariants at each statement
                     private val globals: GlobalVariableMap) : TACMemSplitter {

    /* For memory load and store */
    private val memTACMap: MutableMap<LocatedSbfInstruction, TACMemSplitter.LoadOrStoreInfo> = mutableMapOf()
    /* For memcpy/memcmp */
    private val memInstTACMap: MutableMap<LocatedSbfInstruction, TACMemSplitter.MemInstInfo> = mutableMapOf()
    /* For summarized calls */
    private val callTACMap: MutableMap<LocatedSbfInstruction, List<TACMemSplitter.SummaryArgInfo>> = mutableMapOf()

    init {
        // pre-compute [memTACMap], [memInstTACMap], and [callTACMap] using the Memory domain results
        populateTACMaps()
    }

    override fun getTACMemory(locInst: LocatedSbfInstruction): TACMemSplitter.LoadOrStoreInfo? {
        check(locInst.inst is SbfInstruction.Mem) {"precondition of getTACMemory fails"}
        return memTACMap[locInst]
    }

    override fun getTACMemoryFromMemIntrinsic(locInst: LocatedSbfInstruction): TACMemSplitter.MemInstInfo?  {
        check(locInst.inst is SbfInstruction.Call) {"precondition of getTACMemory fails"}
        return memInstTACMap[locInst]
    }

    override fun getTACMemoryFromSummary(locInst: LocatedSbfInstruction): List<TACMemSplitter.SummaryArgInfo>? {
        check(locInst.inst is SbfInstruction.Call) {"precondition of getTACMemory fails"}
        return callTACMap[locInst]
    }

    /* Private methods */

    sealed class PTAMemoryInfo

    /**
     * Given a Deref *(r+o) from a load or store instruction:
     * @param c is the cell pointed by r+o.
     * @param isStack: whether c.node represents the program stack or not.
     * @param killedFields: list of overlapping cells killed by the pointer analysis during the transfer function of store
     */
    data class PTALoadOrStoreInfo(val c: PTACell,
                                  val isStack: Boolean,
                                  val killedFields: List<Pair<PTANode, PTAField>>): PTAMemoryInfo() {
        init {
            if (c.node.isForwarding()) {
                throw TACTranslationError("PTALoadOrStoreInfo should take only resolved cells")
            }
        }
    }

    /**
     * Given memcpy(src, dst, len), memcmp(src, dst, len), or memmove(src, dst, len):
     * @param dstC is the cell pointed by dst pointer
     * @param srcC is the cell pointed by the source pointer
     * @param length is value of len
     * @param killedFields: list of overlapping cells killed by the pointer analysis during a memory transfer function.
     */
    data class PTAMemoryInstInfo(val dstC: PTACell, val isDstStack: Boolean,
                                 val srcC: PTACell, val isSrcStack: Boolean,
                                 val length: Long?,
                                 val killedFields: List<Pair<PTANode, PTAField>>): PTAMemoryInfo() {
        init {
            if (dstC.node.isForwarding()) {
                throw TACTranslationError("PTAMemoryInstInfo should take only resolved cells (1)")
            }
            if (srcC.node.isForwarding()) {
                throw TACTranslationError("PTAMemoryInstInfo should take only resolved cells (2)")
            }
        }
    }

    data class PTAMemsetInstInfo(val c: PTACell, val isStack: Boolean,
                                 val storedVal: Long?, val length: Long?,
                                 val killedFields: List<Pair<PTANode, PTAField>>): PTAMemoryInfo() {
        init {
            if (c.node.isForwarding()) {
                throw TACTranslationError("PTAMemsetInstInfo should take only resolved cells")
            }
        }
    }

    /**
     * A summary expression such as (*[width])([r]+[offset]):[ty] is converted to a [PTACallModifiedField] object.
     *
     * Let r point to a cell = (n, offset) then
     * - @params [n] is the node
     * - @params [f] is the field represented by offset+4 and [width]
     **/
    data class PTACallModifiedField(val r: SbfRegister, val offset: Long, val width: Byte, val allocatedSpace: ULong,
                                    val n: PTANode, val f: PTAField,
                                    val ty: MemSummaryArgumentType, val isStack: Boolean) {
        init {
            if (n.isForwarding()) {
                throw TACTranslationError("PTACallModifiedField should take only resolved nodes")
            }
        }
    }
    data class PTACallInfo(val modifiedFields: List<PTACallModifiedField>): PTAMemoryInfo()

    /**
     * Populate [memTACMap], [callTACMap], and [memInstTACMap]
     *
     * Since invariants are only stored at the level of basic block,
     * we need to rebuild them for each statement, so we can map each memory instruction
     * to a cell in the global points-to graph.
     *
     * - If the memory instruction accesses the stack, which is tracked in a flow-sensitive manner, then the TAC encoding
     * takes place when the instruction is re-analyzed. This is needed because the stack can change before the analysis of the basic block ends.
     * - If the memory instruction accesses other any memory region, which is tracked in a flow-insensitive manner, then the TAC
     * encoding is delayed after a whole pass has been completed over the whole program. This is needed because bla blab
     **/
    private fun populateTACMaps() {
        val start = System.currentTimeMillis()
        sbfLogger.info { "Re-running memory analysis to generate info at each statement" }
        val listener = MemoryPartitioningListener(::encodePTAtoTAC, analysis.memSummaries, globals)
        for (block in cfg.getBlocks().values) {
            val absVal = analysis.getPre(block.getLabel())
            if (absVal == null || absVal.isBottom())  {
                continue
            }
            absVal.analyze(block, globals, analysis.memSummaries, listener)
        }
        val end = System.currentTimeMillis()
        sbfLogger.info { "Finished re-running memory analysis in ${(end - start) / 1000}s" }
    }

    /**
     * Encode all the memory locations (collected in [memInfo]) accessed by [locInst] into TAC variables.
     * This function returns nothing because it updates [memTACMap], [callTACMap], and [memInstTACMap]
     */
    private fun encodePTAtoTAC(locInst: LocatedSbfInstruction, memInfo: PTAMemoryInfo) {
        val inst = locInst.inst
        check(inst is SbfInstruction.Mem || inst is SbfInstruction.Call)
        if (inst is SbfInstruction.Mem) {
            /** load or store instruction **/
            check(memInfo is PTALoadOrStoreInfo)
            {"A memory instruction should be mapped to a PTALoadOrStoreInfo object"}
            memTACMap[locInst] = processLoadOrStore(memInfo, inst)
        } else if (inst is SbfInstruction.Call){
            if (memInfo is PTACallInfo) {
                /**
                 * SBF to SBF call for which a user-provided summary is available
                 * We just extract all TAC variables that are modified by the summary
                 **/
                val summaryArgs = ArrayList<TACMemSplitter.SummaryArgInfo>()
                for (modifiedField in memInfo.modifiedFields) {
                    val n = modifiedField.n
                    val field = modifiedField.f
                    val isStack = modifiedField.isStack
                    val variable = if (isStack) {
                        vFac.getByteStackVar(field.offset)
                    } else {
                        vFac.getByteMapVar(n.createCell(field.offset))
                    }
                    summaryArgs.add(TACMemSplitter.SummaryArgInfo(modifiedField.r, modifiedField.offset, modifiedField.width, modifiedField.allocatedSpace,
                                                                  modifiedField.ty, variable))
                }
                callTACMap[locInst] = summaryArgs
            } else {
                when (SolanaFunction.from(inst.name)) {
                    SolanaFunction.SOL_MEMCPY -> {
                        check(memInfo is PTAMemoryInstInfo){"memcpy expects PTAMemoryInstInfo"}
                        memInstTACMap[locInst] = processMemCopy(memInfo)
                    }
                    SolanaFunction.SOL_MEMCMP -> {
                        check(memInfo is PTAMemoryInstInfo){"memcmp expects PTAMemoryInstInfo"}
                        memInstTACMap[locInst] = processMemCompare(memInfo)
                    }
                    SolanaFunction.SOL_MEMSET -> {
                        check(memInfo is PTAMemsetInstInfo){"memset expects PTAMemsetInstInfo"}
                        memInstTACMap[locInst] = processMemSet(memInfo)
                    }
                    else -> {
                        throw TACTranslationError("EncodePTAToTAC: expected only memcpy, memcmp, or memset")
                    }
                }
            }
        }
    }


    private fun getVarsToHavoc(baseC: PTACell,
                               fields: List<Pair<PTANode, PTAField>>,
                               isStack: Boolean): TACMemSplitter.HavocMemLocations {
        val baseOffset  = baseC.offset
        val res = if (isStack) {
            TACMemSplitter.HavocScalars(fields.map { vFac.getByteStackVar(it.second.offset)})
        } else {
            // Adjust the offsets to be relative to the base
            TACMemSplitter.HavocMapBytes(fields.map { it.second.offset - baseOffset })
        }
        return res
    }

    /**
     * Create [TACMemSplitter.LoadOrStoreInfo] from [PTALoadOrStoreInfo]
     **/
    private fun processLoadOrStore(memInfo: PTALoadOrStoreInfo,
                                   @Suppress("UNUSED_PARAMETER") inst: SbfInstruction.Mem): TACMemSplitter.LoadOrStoreInfo {
        val locationsToHavoc = getVarsToHavoc(memInfo.c, memInfo.killedFields, memInfo.isStack)
        val tacVar = if (memInfo.isStack) {
            vFac.getByteStackVar(memInfo.c.offset)
        } else {
            vFac.getByteMapVar(memInfo.c)
        }
        return TACMemSplitter.LoadOrStoreInfo(tacVar, locationsToHavoc)
    }

    /**
     * Create [TACMemSplitter.MemCmpInfo] object from [PTAMemoryInstInfo].
     **/
    private fun processMemCompare(memInfo: PTAMemoryInstInfo): TACMemSplitter.MemCmpInfo {
        val length = memInfo.length ?: return TACMemSplitter.UnsupportedMemCmpInfo
        val wordSize = SolanaConfig.WordSize.get().toByte()
        return if (!memInfo.isSrcStack && !memInfo.isDstStack) {
            val dstVar = vFac.getByteMapVar(memInfo.dstC)
            val srcVar = vFac.getByteMapVar(memInfo.srcC)
            TACMemSplitter.NonStackMemCmpInfo(dstVar, srcVar, length, wordSize)
        } else if (memInfo.isSrcStack && memInfo.isDstStack) {
            if (!memInfo.srcC.isWordCompatible(length, wordSize) ||
                !memInfo.dstC.isWordCompatible(length, wordSize)) {
                /// We could continue at the expense of enforcing word addressability later
                TACMemSplitter.UnsupportedMemCmpInfo
            } else {
                /* Scalarize both operands: use of scalars for source and destination */
                val srcVars = createStackVarsFromRange(memInfo.srcC.offset, length, wordSize)
                val dstVars = createStackVarsFromRange(memInfo.dstC.offset, length, wordSize)
                TACMemSplitter.StackMemCmpInfo(
                    dstVars, srcVars,
                    Pair(memInfo.srcC.offset, memInfo.srcC.offset + length - 1),
                    Pair(memInfo.dstC.offset, memInfo.dstC.offset + length - 1),
                    length, wordSize
                )
            }
        } else {
            val (stackC, nonStackC) = if (memInfo.isSrcStack) {
                Pair(memInfo.srcC, memInfo.dstC)
            }  else {
                Pair(memInfo.dstC, memInfo.srcC)
            }
            val (stackReg, nonStackReg) = if (memInfo.isSrcStack) {
                // memInfo.srcC corresponds to r2
                // memInfo.dstC corresponds to r1
                Pair(SbfRegister.R2_ARG, SbfRegister.R1_ARG)
            }  else {
                Pair(SbfRegister.R1_ARG, SbfRegister.R2_ARG)
            }
            if (!stackC.isWordCompatible(length, wordSize)) {
                TACMemSplitter.UnsupportedMemCmpInfo
            } else {
                val scalarVars = createStackVarsFromRange(stackC.offset, length, wordSize)
                val byteMapVar = vFac.getByteMapVar(nonStackC)
                TACMemSplitter.MixedRegionsMemCmpInfo(scalarVars, byteMapVar,
                                                      stackReg, nonStackReg,
                                                      Pair(stackC.offset, stackC.offset + length - 1),
                                                      length, wordSize)
            }
        }
    }

    private fun createStackVarsFromRange(start: PTAOffset, length: Long, wordSize: Byte):
        List<TACByteStackVariable> {
        check(length.mod(wordSize.toInt()) == 0) {"precondition of createScalarVarsFromRange"}
        val vars = ArrayList<TACByteStackVariable>()
        for (i in 0 until length step wordSize.toLong()) {
            val srcOffset = start + i
            vars.add(vFac.getByteStackVar(srcOffset))
        }
        return vars
    }

    /**
     *  Create [TACMemSplitter.MemTransferInfo] object from [PTAMemoryInstInfo]
     **/
    private fun processMemCopy(memInfo: PTAMemoryInstInfo): TACMemSplitter.MemTransferInfo {
        val len = memInfo.length
        return if (!memInfo.isSrcStack && !memInfo.isDstStack) {
            val dstVar = vFac.getByteMapVar(memInfo.dstC)
            val srcVar = vFac.getByteMapVar(memInfo.srcC)
            TACMemSplitter.NonStackMemTransferInfo(
                srcVar, dstVar, len /* it can be null */,
                getVarsToHavoc(memInfo.dstC, memInfo.killedFields, false) as TACMemSplitter.HavocMapBytes)
        } else if (memInfo.isSrcStack && memInfo.isDstStack) {
            if (len == null) {
                throw TACTranslationError("cannot TAC translate stack mempcy without static length")
            }
            TACMemSplitter.StackMemTransferInfo(
                Pair(memInfo.srcC.offset, memInfo.srcC.offset + len - 1),
                Pair(memInfo.dstC.offset, memInfo.dstC.offset + len - 1),
                len,
                getVarsToHavoc(memInfo.dstC, memInfo.killedFields, true) as TACMemSplitter.HavocScalars
            )
        } else {
            val srcC = memInfo.srcC
            val dstC = memInfo.dstC
            // One register points to the stack and the other doesn't.
            // We support it as long as the length is statically known.
            if (len != null) {
                check(memInfo.isDstStack xor memInfo.isSrcStack)
                val (stackC, nonStackC) = if (memInfo.isSrcStack) {
                    Pair(srcC, dstC)
                } else {
                    Pair(dstC, srcC)
                }

                if (nonStackC.node.isExactNode()) {
                    // from stack to exact node or vice-versa
                    TACMemSplitter.MixedRegionsMemTransferInfo(
                        vFac.getByteMapVar(nonStackC),
                        Pair(stackC.offset, stackC.offset + len- 1),
                        memInfo.isDstStack,
                        len,
                        getVarsToHavoc(memInfo.dstC, memInfo.killedFields, memInfo.isDstStack)
                    )
                } else if (stackC == srcC) {
                    check(!nonStackC.node.isExactNode())
                    // from stack to summarized node
                    TACMemSplitter.MixedRegionsMemTransferInfo(
                        vFac.getByteMapVar(nonStackC),
                        Pair(stackC.offset, stackC.offset + len - 1),
                        memInfo.isDstStack,
                        len,
                        getVarsToHavoc(memInfo.dstC, memInfo.killedFields, memInfo.isDstStack)
                    )
                } else {
                    // from summarized node to stack
                    check(stackC == dstC)
                    check(!nonStackC.node.isExactNode())
                    TACMemSplitter.MixedRegionsMemTransferInfo(
                        vFac.getByteMapVar(nonStackC),
                        Pair(stackC.offset, stackC.offset + len - 1),
                        true,
                        len,
                        getVarsToHavoc(memInfo.dstC, memInfo.killedFields, true)
                    )
                }
            } else {
                TACMemSplitter.UnsupportedMemTransferInfo
            }
        }
    }


    /**
     *  Create [TACMemSplitter.MemsetInfo] object from [PTAMemsetInstInfo]
     **/
    private fun processMemSet(memInfo: PTAMemsetInstInfo): TACMemSplitter.MemsetInfo {
        val len = memInfo.length ?: return TACMemSplitter.UnsupportedMemsetInfo
        val storedVal = memInfo.storedVal ?: return TACMemSplitter.UnsupportedMemsetInfo

        return if (memInfo.isStack) {
            if (storedVal == 0L) {
                TACMemSplitter.StackZeroMemsetInfo(Pair(memInfo.c.offset, memInfo.c.offset + len - 1), len)
            } else {
                TACMemSplitter.UnsupportedMemsetInfo
            }
        } else {
            val byteMapVar = vFac.getByteMapVar(memInfo.c)
            TACMemSplitter.NonStackMemsetInfo(byteMapVar, storedVal, len)
        }
    }



    /**
     * Recall that the methods instructionEvent are called before and after each instruction is analyzed by the
     * Memory Analysis. Before each instruction is executed, we identify the [PTACell]s being accessed by the
     * instruction and encode them into TAC variables by using [tacEncoder].
     *
     * Currently, we support:
     * - load
     * - store
     * - external function calls for which user-definable summaries are available
     * - memcpy
     * - memcmp
     * - memset
     *
     * We don't support memmove
     **/
    class MemoryPartitioningListener(private val tacEncoder: (locInst: LocatedSbfInstruction, memInfo: PTAMemoryInfo) -> Unit,
                                     private val memSummaries: MemorySummaries,
                                     private val globalsMap: GlobalVariableMap)
        : InstructionListener<MemoryDomain> {
        override fun instructionEvent(locInst: LocatedSbfInstruction, pre: MemoryDomain, post: MemoryDomain) {}

        /**
         * It contains the set of overlapping killed cells by the pointer analysis in the **last** memcpy instruction.
         * This is produced in [instructionEventBefore] and consumed in [instructionEventAfter]
         **/
        private var killedFieldsByMemcpy: List<Pair<PTANode, PTAField>> = listOf()

        // Sanity check
        private fun checkNoOverlaps(n: PTANode, locInst: LocatedSbfInstruction) {
            if (SolanaConfig.OptimisticPTAOverlaps.get()) {
                return
            }

            var lastOffset = Long.MIN_VALUE
            val intervals = ArrayList<Pair<Long,Long>>()
            // pre-condition: getSuccs() returns the list of pair sorted.
            for ((field, _) in n.getSuccs()) {
                val o = field.offset
                val size = field.size
                intervals.add(Pair(o, o + size - 1))
                if (o <= lastOffset) {
                    throw TACTranslationError("Node $n has overlapping offsets [$o, ${o + size -1}] and $lastOffset: " +
                                              "$intervals at instruction ${locInst.inst} at block ${locInst.label}")
                }
                lastOffset = o + size - 1
            }
        }

        /**
         *  Return the list of overlapping fields that were killed by the pointer analysis during the analysis of
         *  a store instruction.
         *  In TAC, we need to havoc the corresponding scalars or byte map locations that represent those fields.
         **/
         private fun getKilledFields(inst: SbfInstruction.Mem, absVal: MemoryDomain): List<Pair<PTANode, PTAField>> {
            check(!inst.isLoad) {"precondition of getKilledFields: $inst is not a store instruction"}

            val g = absVal.getPTAGraph()
            val baseReg = inst.access.baseReg
            val offset  = inst.access.offset
            val width   = inst.access.width
            val baseSc = g.getRegCell(baseReg)
            if (baseSc != null && baseSc.isReified()) {
                val baseC = baseSc.reify()
                val overwrittenFields = g.getOverlapFields(baseC.node.createCell(baseC.offset + offset), width)
                if (overwrittenFields != null) {
                    return overwrittenFields
                }
            }
            if (!SolanaConfig.OptimisticPTAOverlaps.get()) {
                throw TACTranslationError("cannot determine if $inst should havoc some overlap locations")
            }
            return listOf()
         }

        /**
         *  Return the list of fields that were killed by the pointer analysis during the analysis of
         *  a memcpy instruction. If [onlyOverlaps] is enabled then the returned list only contains fields that
         *  partially overlap the range of memcpy.
         *
         *  In TAC, we need to havoc the corresponding scalars or byte map locations that represent those fields.
         **/
         private fun getKilledFields(inst: SbfInstruction.Call, absVal: MemoryDomain,
                                     onlyOverlaps: Boolean = false): List<Pair<PTANode, PTAField>> {
            check(SolanaFunction.from(inst.name) == SolanaFunction.SOL_MEMCPY) {"Expected call getKilledFields on memcpy"}
            val g = absVal.getPTAGraph()
            val scalars = absVal.getScalars()
            val dstSc = g.getRegCell(Value.Reg(SbfRegister.R1_ARG))
            if (dstSc != null && dstSc.isReified()) {
                val dstC = dstSc.reify()
                val len = (scalars.getValue(Value.Reg(SbfRegister.R3_ARG)).get() as? SbfType.NumType)?.value?.get()
                if (len != null) {
                    val overwrittenFields = g.getOverwrittenFieldsByLongCopy(dstC, len)
                    if (overwrittenFields != null) {
                        return if (onlyOverlaps) {
                            overwrittenFields.filter {
                                val offset = it.second.offset
                                (offset < dstC.offset || dstC.offset + len <= offset)
                            }
                        } else {
                            overwrittenFields
                        }
                    }
                }
            }

            if (!SolanaConfig.OptimisticPTAOverlaps.get()) {
                throw TACTranslationError("cannot determine if memcpy should havoc some overlap locations")
            }
            return listOf()
         }

        class MemPartitioningSummaryVisitor(private val absVal: MemoryDomain,
                                            private val globalsMap: GlobalVariableMap) : SummaryVisitor {
            private val sumFields = ArrayList<PTACallModifiedField>()
            private val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
            private val stackNode = absVal.getRegCell(r10, globalsMap)?.node

            init {
                if (stackNode == null) {
                    throw TACTranslationError("memory partitioning failed because cannot find a cell for r10")
                }
            }

            override fun noSummaryFound(locInst: LocatedSbfInstruction) {}

            override fun processReturnArgument(locInst: LocatedSbfInstruction, type: MemSummaryArgumentType) {}

            override fun processArgument(locInst: LocatedSbfInstruction,
                                         reg: SbfRegister,
                                         offset: Long,
                                         width: Byte,
                                         allocatedSpace: ULong,
                                         type: MemSummaryArgumentType) {
                val call = locInst.inst
                check(call is SbfInstruction.Call)
                val r = Value.Reg(reg)
                val symC = absVal.getRegCell(r, globalsMap)
                    ?: throw TACTranslationError("memory partitioning failed because" +
                                                 "cannot find a cell for $r ($call)")
                val c = symC.reify()
                val adjustedC = c.node.createCell(c.offset + offset)
                val resolvedAdjustedC = adjustedC.resolve()
                sumFields.add(PTACallModifiedField(reg, offset, width, allocatedSpace,
                                                   resolvedAdjustedC.node, PTAField(resolvedAdjustedC.offset, width.toShort()),
                                                   type, resolvedAdjustedC.node == stackNode))
            }

            fun getPTAMemInfo() = PTACallInfo(sumFields)
        }

        override fun instructionEventBefore(locInst: LocatedSbfInstruction, pre: MemoryDomain) {
            if (pre.isBottom()) {
                return
            }
            val memInfo =
                when (val inst = locInst.inst) {
                    is SbfInstruction.Mem -> {
                        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
                        val baseReg = inst.access.baseReg
                        val baseC = pre.getRegCell(baseReg, globalsMap)
                            ?: throw TACTranslationError(
                                "memory partitioning failed because" +
                                    "cannot find a cell for $baseReg ($inst) in the local graph ${locInst.label}"
                            )
                        val stackNode = pre.getRegCell(r10, globalsMap)?.node
                            ?: throw TACTranslationError("memory partitioning failed because cannot find a cell for r10")
                        val offset = PTASymOffset(inst.access.offset.toLong())
                        val newOffset = baseC.offset.add(offset)
                        val derefC = baseC.node.createSymCell(newOffset)
                        val concreteDerefC = derefC.reify()
                        if (SolanaConfig.SanityChecks.get()) {
                            if (concreteDerefC.node == stackNode) {
                                checkNoOverlaps(stackNode, locInst)
                            }
                        }
                        val resolvedDerefC = concreteDerefC.resolve()
                        PTALoadOrStoreInfo(resolvedDerefC, resolvedDerefC.node == stackNode,
                                           if (inst.isLoad) { listOf() } else { getKilledFields(inst, pre) })
                    }
                    is SbfInstruction.Call -> {
                        if (SolanaFunction.from(inst.name) == SolanaFunction.SOL_MEMCPY) {
                            killedFieldsByMemcpy = getKilledFields(inst, pre)
                        }
                        null
                    }
                    else -> {
                        null
                    }
                }

            if (memInfo != null) {
                tacEncoder(locInst, memInfo)
            }
        }

        override fun instructionEventAfter(locInst: LocatedSbfInstruction, post: MemoryDomain) {
            val inst = locInst.inst
            if (post.isBottom()) {
                return
            }
            val memInfo =
                when (inst) {
                    is SbfInstruction.Call -> {
                        when (SolanaFunction.from(inst.name)) {
                            SolanaFunction.SOL_MEMCPY, SolanaFunction.SOL_MEMCMP -> {
                                val r1 = Value.Reg(SbfRegister.R1_ARG)
                                val r2 = Value.Reg(SbfRegister.R2_ARG)
                                val r3 = Value.Reg(SbfRegister.R3_ARG)
                                val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
                                val stackNode = post.getRegCell(r10, globalsMap)?.node
                                    ?: throw TACTranslationError("memory partitioning failed because cannot find a cell for r10")
                                val dstC = post.getRegCell(r1, globalsMap)
                                    ?: throw TACTranslationError(
                                        "memory partitioning failed because" +
                                            "cannot find a cell for $r1 ($inst) in the local graph ${locInst.label}"
                                    )
                                val srcC = post.getRegCell(r2, globalsMap)
                                    ?: throw TACTranslationError(
                                        "memory partitioning failed because" +
                                            "cannot find a cell for $r2 ($inst) in the local graph ${locInst.label}"
                                    )
                                val lengthVal = post.getValue(r3).get()
                                val length = if (lengthVal is SbfType.NumType) {
                                    lengthVal.value.get()
                                } else {
                                    null
                                }
                                val concreteSrcC = srcC.reify()
                                val concreteDstC = dstC.reify()
                                if (SolanaConfig.SanityChecks.get()) {
                                    if (concreteDstC.node == stackNode) {
                                        checkNoOverlaps(stackNode, locInst)
                                    }
                                }

                                val resolvedDstC = concreteDstC.resolve()
                                val resolvedSrcC = concreteSrcC.resolve()
                                PTAMemoryInstInfo(
                                    resolvedDstC, resolvedDstC.node == stackNode,
                                    resolvedSrcC, resolvedSrcC.node == stackNode, length,
                                    killedFieldsByMemcpy
                                )
                            }
                            SolanaFunction.SOL_MEMSET -> {
                                val r1 = Value.Reg(SbfRegister.R1_ARG)
                                val r2 = Value.Reg(SbfRegister.R2_ARG)
                                val r3 = Value.Reg(SbfRegister.R3_ARG)
                                val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
                                val stackNode = post.getRegCell(r10, globalsMap)?.node
                                    ?: throw TACTranslationError("memory partitioning failed because cannot find a cell for r10")
                                // process r1
                                val c = post.getRegCell(r1, globalsMap)
                                    ?: throw TACTranslationError(
                                        "memory partitioning failed because" +
                                            "cannot find a cell for $r1 ($inst) in the local graph ${locInst.label}"
                                    )
                                // process r2
                                val v = post.getValue(r2).get()
                                val storedVal = if (v is SbfType.NumType) {
                                    v.value.get()
                                } else {
                                    null
                                }
                                // process r3
                                val lengthVal = post.getValue(r3).get()
                                val length = if (lengthVal is SbfType.NumType) {
                                    lengthVal.value.get()
                                } else {
                                    null
                                }
                                val concreteC = c.reify()
                                if (SolanaConfig.SanityChecks.get()) {
                                    if (concreteC.node == stackNode) {
                                        checkNoOverlaps(stackNode, locInst)
                                    }
                                }
                                val resolvedC = concreteC.resolve()
                                @Suppress("ForbiddenComment")
                                PTAMemsetInstInfo(
                                    resolvedC, resolvedC.node == stackNode,
                                    storedVal,  length,
                                    listOf() /*TODO: infer killed fields by memset*/
                                )
                            }
                            else -> { /* solana system call or any external call */
                                if (memSummaries.getSummary(inst.name) == null) {
                                    null
                                } else {
                                    val vis = MemPartitioningSummaryVisitor(post, globalsMap)
                                    memSummaries.visitSummary(locInst, vis)
                                    vis.getPTAMemInfo()
                                }
                            }
                        }
                    }
                    else -> {
                        null
                    }
                }

            if (memInfo != null) {
                tacEncoder(locInst, memInfo)
            }
        }
    }
}
