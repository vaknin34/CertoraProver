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

/**
 *  Encoding of a sequence of CFGs to a sequence of TAC programs
 *
 *  Both stack and non-stack memory are encoded using "wide" bytes. A __wide__ byte is like a normal byte, but it can contain
 *  a number bigger than a byte. In our case, the number of bytes is fixed to 64 (256 bits) but this will change to 8 (see COMMENT #1).
 *
 *  The use of wide bytes is needed in order to model precisely memcpy.
 *  Usually, a program under verification starts with non-deterministic memory that can
 *  be copied (by memcpy) many times until it is finally de-referenced.
 *  The use of wide bytes allows us to copy all bytes without knowing a-priori how it will be accessed.
 *  The pointer analysis (PTA) try to check that wide bytes are accessed in a sound way (i.e, no aliasing due to overlaps).
 *
 *
 *  COMMENT #1: the translation pretends that all integers are 256 bits.
 *  This is clearly not true in SBF programs but CVT is currently designed to deal only with
 *  256-bits numbers. This will change to 8 bytes.
 *
 *  COMMENT #2: use ByteMap to represent non-stack memory. A ByteMap is just a map from Int to Int.
 *  This means that we need to be careful with aliasing due to overlaps.
 *  Again, the pointer analysis needs to ensure that.
 *
 *  COMMENT #3: TAC encoding of memcmp and memset is tricky, when at least one operand is a ByteMap.
 *  We fix a priori a word size and perform a sequence of ByteLoad instructions.
 *  For this to be sound, we need to remember which memory regions were compared using
 *  a fixed word size and then to port all memory accesses to those regions to be word-addressable.
 *  This is *not* currently implemented.
 **/

import sbf.*
import sbf.analysis.*
import sbf.callgraph.*
import sbf.cfg.*
import sbf.disassembler.*
import sbf.domains.MemSummaryArgumentType
import sbf.domains.MemorySummaries
import sbf.domains.PTAOffset
import sbf.inliner.SBF_CALL_MAX_DEPTH
import sbf.support.SolanaInternalError
import tac.*
import vc.data.*
import com.certora.collect.*
import datastructures.stdcollections.*
import java.math.BigInteger

// TAC annotations for TAC debugging
val SBF_ADDRESS  = tac.MetaKey<Long>("sbf.bytecode.address")
private val DEBUG_INLINED_FUNC_START = tac.MetaKey<String>("debug.sbf.function.start")
private val DEBUG_INLINED_FUNC_END = tac.MetaKey<String>("debug.sbf.function.end")
private val DEBUG_UNREACHABLE_CODE = tac.MetaKey<String>("debug.unreachable_code")
private val DEBUG_EXTERNAL_CALL = tac.MetaKey<String>("debug.external_call")

class TACTranslationError(msg: String): SolanaInternalError("TAC translation error: $msg")

/** If globalAnalysisResults == null then no memory splitting will be done **/
fun sbfCFGsToTAC(program: SbfCallGraph,
                  memSummaries: MemorySummaries,
                  globalAnalysisResults: Map<String, MemoryAnalysis>?): CoreTACProgram {
    val cfg = program.getCallGraphRootSingleOrFail()
    if (cfg.getBlocks().isEmpty()) {
        throw SolanaInternalError("The translation from SBF to TAC failed because the SBF CFG is empty")
    }

    val analysis = if (globalAnalysisResults == null) {
        null
    } else {
        globalAnalysisResults[cfg.getName()]
            ?: throw TACTranslationError("Not analysis results found for ${cfg.getName()}")
    }
    val marshaller = SbfCFGToTAC(cfg, program, memSummaries, analysis, true)
    return marshaller.encode()
}

/** Translate a SBF CFG to a TAC program **/
@Suppress("ForbiddenComment")
internal class SbfCFGToTAC(private val cfg: SbfCFG,
                           // to have access to global info
                            private val program: SbfCallGraph,
                            private val memSummaries: MemorySummaries,
                            private val memoryAnalysis: MemoryAnalysis?,
                            private val isEntryPoint: Boolean) {
    private val blockMap: MutableMap<Label, NBId> = mutableMapOf()
    private val blockGraph = MutableBlockGraph()
    private val code: MutableMap<NBId, List<TACCmd.Simple>> = mutableMapOf()
    val exprBuilder: TACExprBuilder
    private val scratchRegVars: ArrayList<TACSymbol.Var> = arrayListOf()
    // needed to build TypeScope
    private val declaredVars: ArrayList<TACSymbol.Var> = ArrayList()
    // Map PTA cells to TAC names
    private val vFac = TACVariableFactory()
    // Symbolic memory allocators
    private val heapMemAlloc = TACBumpAllocator("TACHeapAllocator", SBF_HEAP_START.toULong(), SBF_HEAP_END.toULong())
    private val accountsAlloc = TACFixedSizeBlockAllocator("TACSolanaAccountAllocator", SBF_INPUT_START.toULong(), MAX_SOLANA_ACCOUNTS.toUShort(), SOLANA_ACCOUNT_SIZE.toULong())
    // Since the input region is large enough we use it also to allocate memory that other external functions might allocate
    private val extMemAlloc = TACBumpAllocator("TACExternalAllocator", SBF_EXTERNAL_START.toULong() , SBF_INPUT_END.toULong())

    // Map a de-referenced pointer to a symbolic variable.
    // The memory analysis guarantees that all pointers that might alias will be mapped to same
    // symbolic variable.
    private val mem: TACMemSplitter
    // To generate TAC identifiers for variables, basic blocks, and satisfy statements
    private var varId: Int = 0
    private var blockId: Int = 0
    private var satisfyId: Int = 0
    private var assertId: Int = 0
    // Only for printing user warnings
    // Unsupported calls. We just keep track of them to reduce the number of user warnings
    private val unsupportedCalls: MutableSet<String> = mutableSetOf()
    private val functionArgInference = FunctionArgumentInference(cfg)
    private val regTypes: IRegisterTypes

    init {
        // It's much cheaper to analyze the whole cfg from scratch with ScalarAnalysis and rebuild invariants at the
        // instruction level than rebuilding invariants at the instruction level with [memoryAnalysis] (because of
        // the pointer domain).
        val scalarAnalysis = ScalarAnalysis(cfg, program.getGlobals(), memSummaries)
        regTypes = AnalysisRegisterTypes(scalarAnalysis)
        val regVars: ArrayList<TACSymbol.Var> = ArrayList(NUM_OF_SBF_REGISTERS)
        for (i in 0 until NUM_OF_SBF_REGISTERS) {
            // FIXME: the bit-width should be 8 bytes instead of 32 bytes
            val v = TACSymbol.Var("r${i}", Tag.Bit256)
            regVars.add(v)
            declaredVars.add(v)
        }
        exprBuilder = TACExprBuilder(regVars)
        mem = if (memoryAnalysis != null) {
            PTAMemSplitter(cfg, vFac, memoryAnalysis, program.getGlobals())
        } else {
            DummyMemSplitter(declaredVars, regTypes)
        }
    }

    private fun mkBlockIdentifier(SbfBB: SbfBasicBlock): NBId {
        val tacBB = BlockIdentifier(blockId++, 0, 0, 0, 0, 0)
        blockGraph[tacBB] = treapSetOf()
        code[tacBB] = mutableListOf()
        blockMap[SbfBB.getLabel()] = tacBB
        return tacBB
    }

    private fun removeBlockIdentifier(SbfBB: Label) {
        val tacBB = blockMap[SbfBB]
        if (tacBB != null ){
            blockGraph.remove(tacBB)
            code.remove(tacBB)
            blockMap.remove(SbfBB)
        }
    }

    private fun getBlockIdentifier(SbfBB: SbfBasicBlock): NBId {
        check(blockMap.contains(SbfBB.getLabel())) {"getBlockIdentifier failed on ${SbfBB.getLabel()}\n\t$SbfBB"}
        val tacBB = blockMap[SbfBB.getLabel()]
        check(tacBB != null)
        return tacBB
    }


    private fun mkFreshIntVar(@Suppress("UNUSED_PARAMETER")bitwidth: Short = 256,
                              prefix: String = "v"): TACSymbol.Var {
        // FIXME: 256-bit integer is hardcoded.
        val v = TACSymbol.Var("$prefix${varId}", Tag.Bit256)
        varId++
        declaredVars.add(v)
        return v
    }

    private fun mkFreshMathIntVar(prefix: String = "v"): TACSymbol.Var {
        val v = TACSymbol.Var("$prefix${varId}", Tag.Int)
        varId++
        declaredVars.add(v)
        return v
    }

    fun mkFreshBoolVar(prefix: String = "v"): TACSymbol.Var {
        val v = TACSymbol.Var("$prefix${varId}", Tag.Bool)
        varId++
        declaredVars.add(v)
        return v
    }

    private fun mkFreshAssertId(): Int {
        assertId++
        return assertId
    }

    private fun mkFreshSatisfyId(): Int {
        satisfyId++
        return satisfyId
    }

    fun mkAssign(lhs: TACSymbol.Var, rhs: TACExpr): TACCmd.Simple.AssigningCmd {
        return TACCmd.Simple.AssigningCmd.AssignExpCmd(lhs,rhs)
    }

    private fun addInitialPreconditions(): List<TACCmd.Simple> {
        val b = mkFreshBoolVar()
        val r10 = exprBuilder.mkVar(SbfRegister.R10_STACK_POINTER)
        // r10 points to the end of the stack frame
        return listOf(
            mkAssign(b, exprBuilder.mkBinRelExp(CondOp.EQ, TACExpr.Sym.Var(r10), SBF_STACK_START + SBF_STACK_FRAME_SIZE)),
            TACCmd.Simple.AssumeCmd(b))
    }

    private fun inRange(v: TACSymbol.Var, lb: Long, ub: Long, isUnsigned: Boolean = true) =
        inRange(v, lb.toBigInteger(), ub.toBigInteger(), isUnsigned)

    private fun inRange(v: TACSymbol.Var, lb: BigInteger, ub: BigInteger, isUnsigned: Boolean = true): List<TACCmd.Simple>{
        val lbBool = mkFreshBoolVar()
        val ubBool = mkFreshBoolVar()
        return if (isUnsigned) {
            listOf(
                mkAssign(lbBool, exprBuilder.mkBinRelExp(CondOp.GE, v.asSym(), lb)),
                TACCmd.Simple.AssumeCmd(lbBool),
                mkAssign(ubBool, exprBuilder.mkBinRelExp(CondOp.LT, v.asSym(), ub)),
                TACCmd.Simple.AssumeCmd(ubBool)
            )
        } else {
            listOf(
                mkAssign(lbBool, exprBuilder.mkBinRelExp(CondOp.SGE, v.asSym(), lb)),
                TACCmd.Simple.AssumeCmd(lbBool),
                mkAssign(ubBool, exprBuilder.mkBinRelExp(CondOp.SLT, v.asSym(), ub)),
                TACCmd.Simple.AssumeCmd(ubBool)
            )
        }
    }

    /**
     *  Add extra assumptions based on memory layout:
     *        ----------------------------------------------------------------
     *       |      CODE    |       STACK        |      HEAP    |  INPUT   |
     *        ----------------------------------------------------------------
     *  0x100000000     0x200000000         0x30000000     0x40000000        ?
     **/
    private fun addMemoryLayoutAssumptions(ptr: TACSymbol.Var, region: SbfType?):
            List<TACCmd.Simple> {

        if (!SolanaConfig.AddMemLayoutAssumptions.get()) {
            return listOf()
        }

        if (region is SbfType.NumType) {
            return listOf()
        }

        if (region is SbfType.PointerType.Global) {
            // Is there a known range of addresses for global variables?
            return listOf()
        }

        val lb = if (region is SbfType.PointerType) {
            when (region) {
                is SbfType.PointerType.Stack -> SBF_STACK_START
                is SbfType.PointerType.Input -> SBF_INPUT_START
                else -> {
                    check(region is SbfType.PointerType.Heap)
                    SBF_HEAP_START
                }
            }
        } else {
            // REVISIT: global variables have lower addresses than SBF_CODE_START
            //SBF_CODE_START
            0L
        }

        val ub = if (region is SbfType.PointerType) {
            when (region) {
                is SbfType.PointerType.Stack -> {
                    SBF_STACK_START +  (SBF_STACK_FRAME_SIZE * SBF_CALL_MAX_DEPTH)
                }
                is SbfType.PointerType.Input -> {
                    SBF_INPUT_END
                }
                else -> {
                    check(region is SbfType.PointerType.Heap)
                    SBF_HEAP_END
                }
            }
        } else {
            SBF_INPUT_END
        }

        return inRange(ptr, lb, ub)
    }

    private fun translateBin(inst: SbfInstruction.Bin, useMathInt: Boolean): List<TACCmd.Simple> {
        return if (inst.op == BinOp.MOV) {
            listOf(mkAssign(exprBuilder.mkVar(inst.dst), exprBuilder.mkExprSym(inst.v)))
        } else {
            if (!inst.is64) {
                throw TACTranslationError("TAC encoding of 32-bit $inst not supported")
            }
            val op1 = exprBuilder.mkVar(inst.dst)
            val op2 = exprBuilder.mkExprSym(inst.v)
            val cmds = mutableListOf<TACCmd.Simple>()

            if (SolanaConfig.UseTACMathInt.get() &&
                (useMathInt || inst.metaData.getVal(SbfMeta.ADD_WITH_OVERFLOW) != null)) {
                val x = mkFreshMathIntVar()
                val y = mkFreshMathIntVar()
                val z = mkFreshMathIntVar()
                cmds.add(promoteToMathInt(op1.asSym(), x))
                cmds.add(promoteToMathInt(op2, y))
                cmds.add(mkAssign(z, exprBuilder.mkBinExpr(inst.op, x.asSym(), y.asSym(), useMathInt = true)))
                cmds.add(narrowFromMathInt(z.asSym(), op1))
            } else {
                cmds.add(mkAssign(op1, exprBuilder.mkBinExpr(inst.op, op1.asSym(), op2, useMathInt = false)))
            }
            cmds
        }
    }

    private fun translateUn(inst: SbfInstruction.Un): List<TACCmd.Simple> {
        if (inst.op == UnOp.NEG) {
            if (!inst.is64) {
              throw TACTranslationError("TAC encoding of 32-bit $inst not supported")
            }
            val lhs = exprBuilder.mkVar(inst.dst)
            val rhs = exprBuilder.mkUnExpr(UnOp.NEG, inst.dst)
            return listOf(mkAssign(lhs, rhs))
        } else {
            // we don't support UnOp.BE16/32/64, UnOp.LE16/32/64
            throw TACTranslationError("Unsupported $inst")
        }
    }

    private fun translateSelect(inst: SbfInstruction.Select): List<TACCmd.Simple> {
        val newCmds = mutableListOf<TACCmd.Simple>()

        val overflowCond = inst.metaData.getVal(SbfMeta.PROMOTED_ADD_WITH_OVERFLOW_CHECK)
        val (tacOverflowCond, tacOverflowVar) = if (SolanaConfig.TACPromoteOverflow.get() && overflowCond != null) {
            // See comments from translateAssume
            newCmds.add(makeDebugExtCallAnnot("overflow_check"))
            val overflowCondTac = translateCond(overflowCond, bitwidth = 64)
            overflowCondTac to overflowCondTac.getRhs().filterIsInstance<TACSymbol.Var>().singleOrNull()
        }  else {
            translateCond(inst.cond) to null
        }
        newCmds.add(tacOverflowCond)
        newCmds.add(mkAssign(exprBuilder.mkVar(inst.dst), TACExpr.TernaryExp.Ite(TACExpr.Sym.Var(tacOverflowCond.lhs),
                                                                      exprBuilder.mkExprSym(inst.trueVal),
                                                                      exprBuilder.mkExprSym(inst.falseVal) )))

        // This is another 64 vs 256-bit arithmetic fix. See comments from `translateAssume`
        if (tacOverflowVar != null) {
            newCmds.add(mkAssign(tacOverflowVar, exprBuilder.mask64(tacOverflowVar.asSym())))
        }

        return newCmds
    }

    private fun translateHavoc(inst: SbfInstruction.Havoc): List<TACCmd.Simple> {
        return listOf(TACCmd.Simple.AssigningCmd.AssignHavocCmd(exprBuilder.mkVar(inst.dst)))
    }

    private fun translateExit(): List<TACCmd.Simple> {
        // In SBF, the exit command does not have parameter
        // Here we create a return instruction that returns r0
        return listOf(TACCmd.Simple.ReturnSymCmd(exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE)))
    }

    private fun translateCond(cond: Condition, bitwidth: Short = 256): TACCmd.Simple.AssigningCmd {
        val tacLhs = mkFreshBoolVar()
        val leftE = exprBuilder.mkExprSym(cond.left)
        val rightE = if (cond.right is Value.Imm) {
            exprBuilder.mkConst(cond.right, useTwosComplement = true, bitwidth).asSym()
        } else {
            exprBuilder.mkExprSym(cond.right)
        }
        val tacRhs = exprBuilder.mkBinRelExp(cond.op, leftE, rightE)
        return mkAssign(tacLhs, tacRhs)
    }

    /** Return true if [locInst] is an assume instruction and its condition is evaluated semantically to true **/
    private fun isTautology(locInst: LocatedSbfInstruction): Boolean {
        val inst = locInst.inst
        check(inst is SbfInstruction.Assume) {"isRedundantAssume expects an assume instruction instead of $inst"}

        val left = inst.cond.left
        val right = inst.cond.right
        val op = inst.cond.op

        val leftTy = regTypes.typeAtInstruction(locInst, left.r)
        if (leftTy is SbfType.NumType) {
            val leftVal = leftTy.value
            val rightVal = when(right) {
                is Value.Reg ->  {
                    val rightTy = regTypes.typeAtInstruction(locInst, right.r)
                    if (rightTy is SbfType.NumType) {
                        rightTy.value
                    } else {
                        null
                    }
                }
                is Value.Imm -> {
                    ConstantNum(right.v.toLong())
                }
            }
            if (rightVal != null) {
                return leftVal.assume(op, rightVal).isTrue()
            }
        }
        return false
    }

    /** Given a lowered assume it finds its corresponding jump instruction **/
    private fun getJumpFromLoweredAssume(locInst: LocatedSbfInstruction): SbfInstruction.Jump.ConditionalJump? {
        val inst = locInst.inst
        check(inst is SbfInstruction.Assume){"getJumpFromLoweredAssume expects an Assume instead of $inst"}

        if (locInst.pos != 0) {
            return null
        }

        if (inst.metaData.getVal(SbfMeta.LOWERED_ASSUME) == null) {
            return null
        }

        val b = cfg.getBlock(locInst.label)
        check(b != null) { "getJumpFromLoweredAssume cannot find block ${locInst.label}" }
        val predB = b.getPreds().singleOrNull() ?: return null
        val predTerminatorInst = predB.getTerminator()
        if (predTerminatorInst is SbfInstruction.Jump.ConditionalJump) {
            val predCond = if (predTerminatorInst.target == b.getLabel()) {
                predTerminatorInst.cond
            } else {
                predTerminatorInst.cond.negate()
            }
            if (predCond == inst.cond) {
                return predTerminatorInst
            }
        }
        return null
    }

    /**
     * During the CFG construction, we lower conditional jumps into assume instructions by adding them in the successors.
     * All these assume instructions are annotated with LOWERED_ASSUME instructions.
     *
     * This function returns true if [locInst] is one of these LOWERED_ASSUME instructions and can be skipped by TAC encoding
     * while preserving the original semantics. Note that not all LOWERED_ASSUME instructions are redundant because some
     * of them are generated by slicing, and we need to keep those.
     */
    private fun translateAssume(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        if (isTautology(locInst)) {
            return listOf()
        }

        val newCmds: MutableList<TACCmd.Simple> = mutableListOf()

        val jumpInst = getJumpFromLoweredAssume(locInst)
        if (jumpInst != null) {
            // This is another 64 vs 256-bit arithmetic fix similar to the one we do in `translateSelect`
            // Given this code
            // ```
            //    if (x >= 2^64) {
            //          A
            //    } else {
            //          B
            //    }
            // ```
            // We know that the `if` condition is checking whether `x` overflows or not.
            // This fix ensures that after the overflow check has being done (i.e., A and B) x fits in 64 bits.
            //
            val overflowCond = jumpInst.metaData.getVal(SbfMeta.PROMOTED_ADD_WITH_OVERFLOW_CHECK)
            if (SolanaConfig.TACPromoteOverflow.get() && overflowCond != null) {
                val x = exprBuilder.mkVar(overflowCond.left)
                newCmds.add(mkAssign(x, exprBuilder.mask64(x.asSym())))
            }
        } else {
            val inst = locInst.inst as SbfInstruction.Assume
            val cmd = translateCond(inst.cond)
            newCmds.add(cmd)
            newCmds.add(TACCmd.Simple.AssumeCmd(cmd.lhs))
        }
        return newCmds
    }

    private fun translateAssert(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        check(inst is SbfInstruction.Assert) {"TAC translateAssert did not expect $inst"}

        val newCmds: MutableList<TACCmd.Simple> = mutableListOf()
        val cmd = translateCond(inst.cond)
        newCmds.add(cmd)
        newCmds.add(makeCallTraceAssert(inst, cmd.lhs))
        newCmds.add(TACCmd.Simple.AssertCmd(cmd.lhs, inst.metaData.getVal(SbfMeta.COMMENT).orEmpty(), MetaMap(TACMeta.ASSERT_ID to mkFreshAssertId())))
        return newCmds
    }

    private fun translateSatisfy(inst: SbfInstruction.Call): List<TACCmd.Simple> {
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val condVar = mkFreshBoolVar()
        val cond = TACExpr.TernaryExp.Ite(
            TACExpr.BinRel.Eq(exprBuilder.mkExprSym(r1), TACExpr.zeroExpr),
            TACSymbol.True.asSym(),
            TACSymbol.False.asSym()
        )
        val cmds : MutableList<TACCmd.Simple> = mutableListOf()
        cmds.add(TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, cond))
        cmds.add(makeDebugSatisfyAnnot(inst))
        cmds.add(TACCmd.Simple.AssertCmd(condVar, inst.metaData.getVal(SbfMeta.COMMENT).orEmpty(), MetaMap(TACMeta.SATISFY_ID to mkFreshSatisfyId())))
        return cmds
    }

    @Suppress("ForbiddenMethodCall")
    private fun translateSanity(inst: SbfInstruction.Call): List<TACCmd.Simple> {
        return if (cfg.getName().endsWith(sanitySuffix)) {
            translateSatisfy(inst)
        } else {
            listOf()
        }
    }


    private fun translateJump(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val bb = cfg.getBlock(locInst.label)
        check(bb != null)
        val inst = locInst.inst
        check(inst is SbfInstruction.Jump) {"TAC translateJump expects a jump instead of $inst"}
        val newCmds = mutableListOf<TACCmd.Simple>()
        when (inst) {
            is SbfInstruction.Jump.UnconditionalJump -> {
                check(bb.getSuccs().size == 1){"translateJump failed"}
                val targetBB = cfg.getBlock(inst.target)
                check(targetBB != null){"translateJump cannot find block for ${inst.target}"}
                newCmds.add(TACCmd.Simple.JumpCmd(getBlockIdentifier(targetBB)))
            }
            is SbfInstruction.Jump.ConditionalJump -> {
                check(bb.getSuccs().size == 2){"translateJump failed"}
                val overflowCond = inst.metaData.getVal(SbfMeta.PROMOTED_ADD_WITH_OVERFLOW_CHECK)
                val cmd = if (SolanaConfig.TACPromoteOverflow.get() && overflowCond != null) {
                    /**
                     * We replace the original condition with the metadata's condition.
                     * Thus, by default the SBF code:
                     * ```
                     * z = x + y
                     * if (x > z) { ... }
                     * ```
                     * is translated to :
                     * ```
                     * z = x + y
                     * b = (z >= 2^64)
                     * ```
                     * instead of
                     * ```
                     * z = x + y
                     * b = (x > z)
                     * ```
                     *
                     * If `--solanaTACMathInt true` then is translated to :
                     * ```
                     * z_int = promote(x) + promote(y)
                     * z = narrow(z_int)
                     * b = (z >= 2^64)
                     * ```
                     *   REVISIT: The use of `z` instead of `z_int` in `b = (z >= 2^64)` is sound because we are using
                     *   256-bit TAC registers. However, once we move to 64-bit TAC registers we will need to use `z_int`
                     **/
                    newCmds.add(makeDebugExtCallAnnot("promoted_overflow_check"))
                    translateCond(overflowCond, bitwidth = 64)
                }  else {
                    translateCond(inst.cond)
                }
                newCmds.add(cmd)
                val trueTargetBB = cfg.getBlock(inst.target)
                check(trueTargetBB != null)
                val trueTargetNBId = getBlockIdentifier(trueTargetBB)
                val falseTargetBB = inst.falseTarget?.let { cfg.getBlock(it) }
                check(falseTargetBB != null)
                val falseTargetNBId = getBlockIdentifier(falseTargetBB)
                newCmds.add(TACCmd.Simple.JumpiCmd(trueTargetNBId, falseTargetNBId, cmd.lhs))
            }
        }
        return newCmds
    }

    private fun makeUnreachable(inst: SbfInstruction): List<TACCmd.Simple> {
        return listOf(
            makeDebugUnreachable(inst),
            TACCmd.Simple.AssumeCmd(exprBuilder.mkBoolConst(false))
        )
    }

    // Print TAC annotations

    private fun makeDebugUnreachable(inst: SbfInstruction)  =
        TACCmd.Simple.AnnotationCmd(TACCmd.Simple.AnnotationCmd.Annotation(DEBUG_UNREACHABLE_CODE, "$inst"))

    private fun makeDebugExtCallAnnot(fname: String): TACCmd.Simple =
        TACCmd.Simple.AnnotationCmd(TACCmd.Simple.AnnotationCmd.Annotation(DEBUG_EXTERNAL_CALL, fname))

    private fun makeDebugExtCallAnnot(inst: SbfInstruction.Call): TACCmd.Simple = makeDebugExtCallAnnot(inst.name)

    private fun makeDebugSatisfyAnnot(inst: SbfInstruction.Call): TACCmd.Simple = makeDebugExtCallAnnot(inst)

    private fun makeCallTraceExtCall(inst: SbfInstruction.Call,
                                     symbols: List<TACSymbol.Var>): TACCmd.Simple {
        return SnippetCmd.SolanaSnippetCmd.ExternalCall(inst.name, symbols).toAnnotation()
    }

    private fun makeCallTraceAssert(@Suppress("UNUSED_PARAMETER")inst: SbfInstruction.Assert,
                                    cond: TACSymbol.Var): TACCmd.Simple {
        return SnippetCmd.SolanaSnippetCmd.Assert("assert", cond).toAnnotation()
    }

    private fun getString(locInst: LocatedSbfInstruction, reg: SbfRegister): String {
        return regTypes.typeAtInstruction(locInst, reg).let {
            if (it is SbfType.PointerType.Global && it.global is SbfConstantStringGlobalVariable) {
                it.global.value
            } else {
                sbfLogger.warn {
                        "Cannot identify statically the content of the string associated with ${locInst.inst}. " +
                        "Generating tag ${locInst.label}#${locInst.pos} instead to be used by the calltrace."
                }
                "${locInst.label}#${locInst.pos}"
            }
        }
    }

    private fun makeCallTraceCexValOrTag(locInst: LocatedSbfInstruction, cexPrintFunction: CVTFunction): TACCmd.Simple {
        val tag = getString(locInst, SbfRegister.R1_ARG)
        return if (cexPrintFunction == CVTFunction.CEX_PRINT_TAG) {
            SnippetCmd.SolanaSnippetCmd.CexPrintTag(tag).toAnnotation()
        } else {
            val usedVars = mutableListOf<TACSymbol.Var>()
            var i = 0
            val numArgs = cexPrintFunction.function.readRegisters.size - 2 /** We skip R1 and R2 **/
            while (i < numArgs) {
                usedVars.add(exprBuilder.mkVar(SbfRegister.getByValue((i + 3).toByte()))) // We start at R3
                i++
            }
            SnippetCmd.SolanaSnippetCmd.CexPrintValues(tag, usedVars).toAnnotation()
        }
    }

    private fun makeCallTraceCexPrintLocation(locInst: LocatedSbfInstruction): TACCmd.Simple {
        val (filepath, lineNumber) = getFilepathAndLineNumber(locInst)
        return SnippetCmd.SolanaSnippetCmd.CexPrintLocation(filepath, lineNumber).toAnnotation()
    }

    private fun makeCallTraceCexAttachLocation(locInst: LocatedSbfInstruction): TACCmd.Simple {
        val (filepath, lineNumber) = getFilepathAndLineNumber(locInst)
        return SnippetCmd.SolanaSnippetCmd.CexAttachLocation(filepath, lineNumber).toAnnotation()
    }

    /** Read the filepath from the first two registers and the line number from the third one. */
    private fun getFilepathAndLineNumber(locInst: LocatedSbfInstruction): Pair<String, UInt> {
        val filepath = getString(locInst, SbfRegister.R1_ARG)
        // The first two registers are for the filepath (pointer + length), the third is for the line number.
        val value = (regTypes.typeAtInstruction(locInst, SbfRegister.R3_ARG) as? SbfType.NumType)?.value?.get()
        val lineNumber = if (value == null) {
            sbfLogger.warn {
                "Cannot identify statically the content of the string associated with ${locInst.inst}. " +
                "Returning 1 instead to be used by the calltrace."
            }
            1U
        } else {
            value.toUInt()
        }
        return filepath to lineNumber
    }

    private fun makeCallTraceCexString(locInst: LocatedSbfInstruction): TACCmd.Simple {
        val tag = getString(locInst, SbfRegister.R1_ARG)
        val str = getString(locInst, SbfRegister.R3_ARG)
        return SnippetCmd.SolanaSnippetCmd.CexPrintTag("$tag: $str").toAnnotation()
    }

    private fun startFunction(name: String, msg: String = ""): TACCmd.Simple {
        return TACCmd.Simple.AnnotationCmd(
            TACCmd.Simple.AnnotationCmd.Annotation(
                DEBUG_INLINED_FUNC_START,
                "$name$msg"
            )
        )
    }

    private fun endFunction(name: String, msg: String = ""): TACCmd.Simple {
        return TACCmd.Simple.AnnotationCmd(
            TACCmd.Simple.AnnotationCmd.Annotation(
                DEBUG_INLINED_FUNC_END,
                "$name$msg"
            )
        )
    }

    /** Add instructions in [cmds] that havoc [scalars] variables **/
    private fun havocScalars(scalars: List<TACSymbol.Var>,
                             cmds: MutableList<TACCmd.Simple>) {
        scalars.forEach {
            cmds.add(TACCmd.Simple.AssigningCmd.AssignHavocCmd(it))
        }
    }

    /** Add instructions in [cmds] that havoc the indexes [loc] + [indexes] of the byte map [base] **/
    private fun havocByteMapLocation(indexes:  List<PTAOffset>,  base: TACByteMapVariable, loc: TACSymbol.Var,
                                     cmds: MutableList<TACCmd.Simple>) {
        val values = ArrayList<TACSymbol.Var>()
        indexes.forEach { _ ->
            val value = mkFreshIntVar(256)
            cmds.add(TACCmd.Simple.AssigningCmd.AssignHavocCmd(value))
            values.add(value)
        }
       emitTACMapStores(
            base,
            loc,
            indexes,
            values,
            cmds
        )
    }

    /** Emit TAC code for memcpy from non-stack to non-stack **/
    private fun emitMemCopyNonStackToNonStack(info: TACMemSplitter.NonStackMemTransferInfo): List<TACCmd.Simple> {
        val cmds: MutableList<TACCmd.Simple> = mutableListOf()
        cmds.add(startFunction("memcpy","(dst=nonStack, src=nonStack, len=${info.length})"))

        val dstOffsetSym = exprBuilder.mkVar(SbfRegister.R1_ARG)
        val srcOffsetSym = exprBuilder.mkVar(SbfRegister.R2_ARG)
        val length = info.length
        val lengthSym = if (length == null) {
            exprBuilder.mkVar(SbfRegister.R3_ARG)
        } else {
            exprBuilder.mkConst(length)
        }
        val src = info.source
        val dst = info.destination
        havocByteMapLocation(info.locationsToHavoc.fields, dst, exprBuilder.mkVar(SbfRegister.R1_ARG), cmds)
        cmds.add(TACCmd.Simple.ByteLongCopy(dstOffsetSym, srcOffsetSym, lengthSym, dst.tacVar, src.tacVar))
        cmds.add(endFunction("memcpy"))
        return cmds
    }

    /** Emit TAC code for memcpy from stack to stack **/
    private fun emitMemCopyStackToStack(info: TACMemSplitter.StackMemTransferInfo): List<TACCmd.Simple> {
        val len = info.length
        val srcRange = info.sourceRange
        val dstRange = info.destinationRange
        val cmds: MutableList<TACCmd.Simple> = mutableListOf()
        cmds.add(startFunction("memcpy","(dst=Stack$dstRange, src=Stack$srcRange, len=$len)"))
        havocScalars(info.locationsToHavoc.vars.map{ it.tacVar }, cmds)
        for (i in 0 until len) {
            val srcOffset = srcRange.first + i
            val dstOffset = dstRange.first + i
            val srcBV = vFac.getByteStackVar(srcOffset)
            val dstBV = vFac.getByteStackVar(dstOffset)
            cmds.add(mkAssign(dstBV.tacVar, srcBV.tacVar.asSym()))
        }
        cmds.add(endFunction("memcpy"))
        return cmds
    }

    /** Emit TAC code for memcpy from non-stack to stack **/
    private fun emitMemCopyNonStackToStack(info: TACMemSplitter.MixedRegionsMemTransferInfo): List<TACCmd.Simple> {
        check(info.isDestStack) {"precondition for emitMemCopyNonStackToStack"}
        val cmds: MutableList<TACCmd.Simple> = mutableListOf()
        cmds.add(startFunction("memcpy", "(dst=Stack${info.stackOpRange}, src=non-stack, len=${info.length})"))
        havocScalars((info.locationsToHavoc as TACMemSplitter.HavocScalars).vars.map{ it.tacVar }, cmds)
        val dstRange = info.stackOpRange
        val byteVarsAtSrc = emitTACMapLoads(info.byteMap, exprBuilder.mkVar(SbfRegister.R2_ARG), 1, info.length, cmds)
        byteVarsAtSrc.forEachIndexed { i, srcV ->
            val dstOffset = dstRange.first + i
            val dstBV = vFac.getByteStackVar(dstOffset)
            cmds.add(mkAssign(dstBV.tacVar, srcV.asSym()))
        }
        cmds.add(endFunction("memcpy"))
        return cmds
    }

    /** Emit TAC code for memcpy from stack to non-stack **/
    private fun emitMemCopyStackToNonStack(info: TACMemSplitter.MixedRegionsMemTransferInfo): List<TACCmd.Simple> {
        check(!info.isDestStack) {"precondition for emitMemCopyStackToNonStack"}
        val cmds: MutableList<TACCmd.Simple> = mutableListOf()
        cmds.add(startFunction("memcpy", "(dst=non-stack, src=Stack${info.stackOpRange}, len=${info.length})"))
        havocByteMapLocation((info.locationsToHavoc as TACMemSplitter.HavocMapBytes).fields, info.byteMap, exprBuilder.mkVar(SbfRegister.R1_ARG), cmds)
        val srcRange = info.stackOpRange
        val len = info.length
        for (i in 0 until len) {
            val srcOffset = srcRange.first + i
            val srcBV = vFac.getByteStackVar(srcOffset)
            emitTACMapStores(info.byteMap, exprBuilder.mkVar(SbfRegister.R1_ARG),
                listOf(i), listOf(srcBV.tacVar), cmds)

        }
        cmds.add(endFunction("memcpy"))
        return cmds
    }

    /**
     * Translate a `memcpy` instruction to TAC.
     **/
    private fun translateMemCopy(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        check(inst is SbfInstruction.Call) {"TAC translateMemCopy expects a call instead of $inst"}
        val info = mem.getTACMemoryFromMemIntrinsic(locInst)
        if (info == null) {
            return makeUnreachable(inst)
        } else {
            check(info is TACMemSplitter.MemTransferInfo) { "$inst expects MemTransferInfo" }
            return when (info) {
                is TACMemSplitter.UnsupportedMemTransferInfo -> {
                    // We couldn't generate TAC code for the memcpy instruction.
                    // This might affect soundness because we don't havoc the destination.
                    sbfLogger.warn { "Unsupported TAC translation of $inst in block ${locInst.label}" }
                    listOf()
                }
                is TACMemSplitter.NonStackMemTransferInfo -> {
                    // CASE 1: non-stack to non-stack
                    emitMemCopyNonStackToNonStack(info)
                }
                is TACMemSplitter.StackMemTransferInfo  -> {
                    // CASE 2: stack to stack
                    emitMemCopyStackToStack(info)
                }
                is TACMemSplitter.MixedRegionsMemTransferInfo -> {
                    if (info.isDestStack) {
                        // CASE 3: from non-stack to stack
                        emitMemCopyNonStackToStack(info)
                    } else {
                        // CASE 4: from stack to non-stack
                        emitMemCopyStackToNonStack(info)
                    }
                }
            }
        }
    }

    /** Emit TAC code for index = [base] + [offset] **/
    private fun computeTACMapIndex(base: TACSymbol.Var, offset: Long, cmds: MutableList<TACCmd.Simple>): TACSymbol.Var {
        val index = mkFreshIntVar(256)
        cmds.add(mkAssign(index, exprBuilder.mkAddExpr(base.asSym(), exprBuilder.mkConst(offset).asSym(), useMathInt = false)))
        return index
    }

    /**
     * Emit TAC code that writes [values] in [byteMap] starting at [base] with [offsets]
     * [offsets] are already relative to [base]
     */
    private fun emitTACMapStores(byteMap: TACByteMapVariable,
                                 base: TACSymbol.Var,
                                 offsets: List<PTAOffset>,
                                 values: List<TACSymbol.Var>,
                                 cmds: MutableList<TACCmd.Simple>) {
        // precondition: fields are sorted and len(fields) = len(values)
        check(offsets.size == values.size) {"Precondition of emitTACMapStores"}
        for ( (offset, value) in offsets.zip(values)) {
            val loc = computeTACMapIndex(base, offset, cmds)
            // REVISIT: ByteStore assumes 32 bytes are written so the actual width is being ignored
            cmds.add(TACCmd.Simple.AssigningCmd.ByteStore(loc, value, byteMap.tacVar))
        }
    }

    /**
     * Emit TAC code that loads each word from [byteMap] starting at [base] up to [length]
     */
    private fun emitTACMapLoads(byteMap: TACByteMapVariable,
                                base: TACSymbol.Var,
                                wordSize: Byte, length: Long,
                                cmds: MutableList<TACCmd.Simple>): List<TACSymbol.Var> {
        val numOfWords = length.toInt() / wordSize
        val intVars = ArrayList<TACSymbol.Var>(numOfWords)
        for (i in 0 until numOfWords) {
            val loc = computeTACMapIndex(base, wordSize.toLong() * i.toLong(), cmds)
            val x = mkFreshIntVar(256)
            // REVISIT: ByteLoad assumes 32 bytes are read so the actual width (wordSize) is being ignored
            cmds.add(TACCmd.Simple.AssigningCmd.ByteLoad(x, loc, byteMap.tacVar))
            intVars.add(x)
        }
        // We should add at each loop iteration that [loc] cannot be greater than SBF_INPUT_END
        // However, this will add too many constraints to the solver. Instead, we enforce that [base] cannot
        // be greater than SBF_INPUT_END. Note that our solution is still sound, but it might produce spurious
        // counterexamples is numOfWords is too large. In fact, right now this cannot happen since we use 256 bits to
        // represent integers.
        cmds.addAll(addMemoryLayoutAssumptions(base, null))
        return intVars
    }

    /**
     * Emit a TAC expression that evaluates to 0 if [l1] is equal to [l2],
     * otherwise it evaluates to 1
     **/
    private fun emitTACVarsEq(l1: List<TACSymbol.Var>, l2: List<TACSymbol.Var>, cmds: MutableList<TACCmd.Simple>): TACExpr {
        check(l1.size == l2.size) {"Precondition of emitTACVarsEq does not hold: $l1 and $l2 have different sizes."}
        val boolVars = ArrayList<TACSymbol.Var>(l1.size)
        for ((x,y) in l1.zip(l2)) {
            val b = mkFreshBoolVar()
            boolVars.add(b)
            cmds.add(mkAssign(b, TACExpr.BinRel.Eq(x.asSym(), y.asSym())))
        }
        var e: TACExpr = exprBuilder.ZERO.asSym()
        for (b in boolVars.reversed()) {
            e =  TACExpr.TernaryExp.Ite(b.asSym(), e, exprBuilder.ONE.asSym())
        }
        return e
    }

    /**
     *  Translate a `memcmp` instruction to TAC
     *
     *  @param locInst is a memcmp(x,y,len) instruction
     *
     *  FIXME: right now we encode inst in TAC as r0 := (x==y ? 0: 1)
     *  However, the exact semantics of memcmp is
     *  return   0  if x == y
     *  return  <0  if x < y (lexicographically)
     *  return  >0  if x > y (lexicographically)
     */
    private fun translateMemCompare(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        check(inst is SbfInstruction.Call) {"TAC translateMemCopy expects a call instead of $inst"}
        val info = mem.getTACMemoryFromMemIntrinsic(locInst)
        return if (info == null) {
            makeUnreachable(inst)
        } else {
            check(info is TACMemSplitter.MemCmpInfo){"$info is not MemCmpInfo"}
            return when (info) {
                is TACMemSplitter.UnsupportedMemCmpInfo -> {
                    sbfLogger.warn { "TAC encoding of $inst in block ${locInst.label} will be sound but imprecise" }
                    listOf(
                        startFunction("memcmp"),
                        TACCmd.Simple.AssigningCmd.AssignHavocCmd(exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE)),
                        endFunction("memcmp")
                    )
                }
                is TACMemSplitter.NonStackMemCmpInfo -> {
                    val r0 = exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE)
                    val r1 = exprBuilder.mkVar(SbfRegister.R1_ARG)
                    val r2 = exprBuilder.mkVar(SbfRegister.R2_ARG)
                    val cmds: MutableList<TACCmd.Simple> = mutableListOf()
                    cmds.add(startFunction("memcmp"))
                    // Read word-by word from the byte maps because there is no TAC instruction
                    // for comparison of ByteMap.
                    // REVISIT(SOUNDNESS):
                    // Soundness depends on all writes to the two memory regions to access exactly info.wordSize bytes.
                    val op1Vars = emitTACMapLoads(info.op1, r1, info.wordSize, info.length, cmds)
                    val op2Vars = emitTACMapLoads(info.op2, r2, info.wordSize, info.length, cmds)
                    cmds.add(mkAssign(r0,  emitTACVarsEq(op1Vars, op2Vars, cmds)))
                    cmds.add(endFunction("memcmp"))
                    cmds
                }
                is TACMemSplitter.StackMemCmpInfo -> {
                    val r0 = exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE)
                    val cmds: MutableList<TACCmd.Simple> = mutableListOf()
                    cmds.add(startFunction("memcmp", "(op1=Stack${info.op1Range}, op2=Stack${info.op2Range})"))
                    cmds.add(mkAssign(r0, emitTACVarsEq(info.op1.map{it.tacVar}, info.op2.map{it.tacVar}, cmds)))
                    cmds.add(endFunction("memcmp"))
                    cmds
                }
                is TACMemSplitter.MixedRegionsMemCmpInfo -> {
                    val r0 = exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE)
                    // scalars
                    val op1Vars = info.scalars
                    val cmds: MutableList<TACCmd.Simple> = mutableListOf()
                    cmds.add(startFunction("memcmp", "(${info.scalarsReg}=${info.stackOpRange})"))
                    // byte map
                    // Read word-by-word from the byte map to be able to compare with the scalars.
                    // REVISIT(SOUNDNESS):
                    // Soundness depends on all writes to the non-scalar memory region to access exactly info.wordSize bytes.
                    val op2Vars = emitTACMapLoads(info.byteMap, exprBuilder.mkVar(info.byteMapReg), info.wordSize, info.length, cmds)
                    cmds.add(mkAssign(r0, emitTACVarsEq(op1Vars.map{it.tacVar}, op2Vars, cmds)))
                    cmds.add(endFunction("memcmp"))
                    cmds
                }
            }
        }
    }

   /**
    *  Translate a `memset` instruction to TAC
    *
    *  @param locInst is a memset(x,val,len) instruction
    **/
    private fun translateMemSet(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
       val inst = locInst.inst
       check(inst is SbfInstruction.Call) {"TAC translateMemCopy expects a call instead of $inst"}
        val info = mem.getTACMemoryFromMemIntrinsic(locInst)
        return if (info == null) {
            makeUnreachable(inst)
        } else {
            check(info is TACMemSplitter.MemsetInfo){"$info is not MemsetInfo"}
            return when (info) {
                is TACMemSplitter.UnsupportedMemsetInfo -> {
                    // We couldn't generate TAC code for the memset instruction.
                    // This might affect soundness because we don't havoc the destination.
                    sbfLogger.warn { "Unsupported TAC translation of $inst in block ${locInst.label}" }
                    listOf()
                }
                is TACMemSplitter.StackZeroMemsetInfo -> {
                    val len = info.length
                    val range = info.stackOpRange
                    val cmds: MutableList<TACCmd.Simple> = mutableListOf()
                    cmds.add(startFunction("memset", "(Stack($range), 0)"))
                    for (i in 0 until len) {
                        val offset = range.first + i
                        val pv = vFac.getByteStackVar(offset)
                        cmds.add(mkAssign(pv.tacVar, exprBuilder.ZERO.asSym()))
                    }
                    cmds.add(endFunction("memset"))
                    return cmds
                }
                is TACMemSplitter.NonStackMemsetInfo -> {
                    val len = info.length
                    val value = info.value

                    val initMap = vFac.getByteMapVar("memset")
                    val cmds: MutableList<TACCmd.Simple> = mutableListOf()
                    cmds.add(startFunction("memset", "(NonStack, $value, $len)"))
                    // If value != 0 then we create a map that always returns a non-determistic value.
                    // We could have also returned value instead but that would be unsound since for memset we need to
                    // know how the stored value is going to be read (i.e., word size).
                    cmds.add(TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = initMap.tacVar,
                        rhs = TACExpr.MapDefinition(
                            defParams = listOf(TACKeyword.TMP(Tag.Bit256, "!idx").toUnique("!").asSym()),
                            tag = Tag.ByteMap,
                            definition = if (value == 0L) {
                                            exprBuilder.mkConst(value).asSym()
                                         } else {
                                            TACExpr.Unconstrained(Tag.Bit256)
                                         }
                        )
                    ))
                    cmds.add(TACCmd.Simple.ByteLongCopy(
                        srcBase = initMap.tacVar,
                        srcOffset = TACSymbol.Zero,
                        dstBase = info.byteMap.tacVar,
                        dstOffset = exprBuilder.mkVar(SbfRegister.R1_ARG),
                        length = exprBuilder.mkConst(len),
                    ))
                    cmds.add(endFunction("memset"))
                    return cmds
                }
            }
        }
    }
    private fun SbfInstruction.Call.toStartInlinedAnnotation(
        locInst: LocatedSbfInstruction): SbfInlinedFuncStartAnnotation? {
        if (CVTFunction.from(name) != CVTFunction.SAVE_SCRATCH_REGISTERS) {
            return null
        }
        val fnName = metaData.getVal(SbfMeta.INLINED_FUNCTION_NAME) ?: return null
        val callId = metaData.getVal(SbfMeta.CALL_ID)?.toInt() ?: return null

        // These are the observed args across all call sites
        val observedArgs = functionArgInference.inferredArgs(fnName) ?: return null
        // "pad up" to the largest observed register
        val maxArgRegister = observedArgs.keys.maxByOrNull { it.r }?.r
        // Produce a map that associates each register to its uses, including
        // registers we did not see but whose index is smaller than some register
        // we _did_ see
        val args = SbfRegister.funArgRegisters.filter {
            maxArgRegister != null && it <= maxArgRegister
        }.associate {
            val k = Value.Reg(it)
            k to observedArgs[k].orEmpty()
        }

        // We want to indicate in this inlining annotation
        // which registers we actually saw used at _this_ callsite
        val live = functionArgInference.liveAtThisCall(locInst) ?: return null
        val tacArgs = inferredArgsToTACArgs(args, live)

        return SbfInlinedFuncStartAnnotation(
            name = fnName,
            args = tacArgs,
            id = callId
        )
    }

    private fun inferredArgsToTACArgs(
        args: Map<Value.Reg, Set<LocatedSbfInstruction>>,
        live: Set<Value.Reg>
    ): List<Pair<TACSymbol.Var, SbfFuncArgInfo>> {
        return args.toList().sortedBy {  (rVal, _) ->
            rVal.r
        }.map { (reg, uses) ->
            // For each register/set of uses,
            val sort = SbfArgSort.fromSbfType(registerTypeFromUses(uses, reg.r))

            // Indicate if, at this callsite, we actually have a use of [reg]
            val observedUse = reg in live

            exprBuilder.mkVar(reg.r) to SbfFuncArgInfo(
                sort = sort,
                observedUse = observedUse
            )
        }
    }

    private fun registerTypeFromUses(uses: Collection<LocatedSbfInstruction>, r: SbfRegister): SbfType {
        return uses.map {
            regTypes.typeAtInstruction(it, r)
        }.fold(SbfType.Bottom as SbfType) { t1, t2 ->
            t1.join(t2)
        }
    }

    private fun SbfInstruction.Call.toEndInlineAnnotation(): SbfInlinedFuncEndAnnotation? {
        if (CVTFunction.from(name) != CVTFunction.RESTORE_SCRATCH_REGISTERS) {
            return null
        }
        val fnName = metaData.getVal(SbfMeta.INLINED_FUNCTION_NAME) ?: return null
        val callId = metaData.getVal(SbfMeta.CALL_ID)?.toInt() ?: return null
        val retVar = exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE)
        return SbfInlinedFuncEndAnnotation(
            name = fnName,
            id = callId,
            retVal = retVar
        )
    }

    private fun promoteToMathInt(from: TACExpr.Sym, to: TACSymbol.Var): TACCmd.Simple.AssigningCmd.AssignExpCmd {
        check(from.tag != null) {"promoteToMathInt cannot find tag for $from"}
        return TACCmd.Simple.AssigningCmd.AssignExpCmd(
            lhs = to,
            rhs = TACExpr.Apply(
                f = TACExpr.TACFunctionSym.BuiltIn(
                    TACBuiltInFunction.SafeMathPromotion(from.tag!!)
                ),
                ops = listOf(from),
                tag = Tag.Int
            )
        )
    }

    private fun narrowFromMathInt(from: TACExpr.Sym, to: TACSymbol.Var, toTag: Tag.Bits = Tag.Bit256): TACCmd.Simple.AssigningCmd.AssignExpCmd {
        check(from.tag == Tag.Int) {"narrowToBit expects an Int variable"}
        return TACCmd.Simple.AssigningCmd.AssignExpCmd(
            lhs = to,
            rhs = TACExpr.Apply(
                TACExpr.TACFunctionSym.BuiltIn(TACBuiltInFunction.SafeMathNarrow(toTag)),
                listOf(from),
                toTag
            )
        )
    }

    /** res = high << 64 + low **/
    private fun mergeU128(low: TACExpr.Sym, high: TACExpr.Sym,
                          cmds: MutableList<TACCmd.Simple>): TACSymbol.Var {
        val res = mkFreshIntVar()
        val c64E = exprBuilder.SIXTY_FOUR.asSym()
        cmds.add(mkAssign(res, TACExpr.Vec.Add(listOf(TACExpr.BinOp.ShiftLeft(high, c64E), low))))
        return res
    }
    /** res = high << 64 + low **/
    private fun mergeU128(res: TACSymbol.Var, low: TACExpr.Sym, high: TACExpr.Sym): TACCmd.Simple.AssigningCmd {
        val c64E = exprBuilder.SIXTY_FOUR.asSym()
        return mkAssign(res, TACExpr.Vec.Add(listOf(TACExpr.BinOp.ShiftLeft(high, c64E), low)))
    }

    /** res = (w4 << 192) + (w3 << 128) + (w2 << 64) + w1 */
    private fun mergeU256(res: TACSymbol.Var, w1: TACExpr.Sym, w2: TACExpr.Sym, w3:TACExpr.Sym, w4: TACExpr.Sym): TACCmd.Simple.AssigningCmd {
        val c64  = exprBuilder.SIXTY_FOUR.asSym()
        val c128 = exprBuilder.mkConst(128, false, 256).asSym()
        val c196 = exprBuilder.mkConst(196, false, 256).asSym()
        return mkAssign(res, TACExpr.Vec.Add(listOf(
                                TACExpr.BinOp.ShiftLeft(w4, c196),
                                TACExpr.BinOp.ShiftLeft(w3, c128),
                                TACExpr.BinOp.ShiftLeft(w2, c64),
                                w1)))
    }

    /**
     *  low = e & MASK64
     *  high = e >> 64
     */
    private fun splitU128(e: TACSymbol.Var, low: TACSymbol.Var, high: TACSymbol.Var,
                          cmds: MutableList<TACCmd.Simple>) {
        val c64E = exprBuilder.SIXTY_FOUR.asSym()
        val twoPowerOf128 = BigInteger.TWO.pow(128).asTACExpr()
        val x = mkFreshIntVar()
        cmds.add(mkAssign(x, TACExpr.BinOp.Mod(e.asSym(), twoPowerOf128)))
        cmds.add(mkAssign(low, exprBuilder.mask64(x.asSym())))
        cmds.add(mkAssign(high, TACExpr.BinOp.ShiftRightLogical(x.asSym(), c64E)))
    }

    /** Get the symbolic TAC variables corresponding to the low and high bits of the returned u128 value **/
    private fun getLowAndHighFromU128(locInst: LocatedSbfInstruction): Pair<TACVariable, TACVariable>? {
        val summaryArgs = mem.getTACMemoryFromSummary(locInst) ?: return null
        if (summaryArgs.size != 2) {
            return null
        }
        val resLow  = summaryArgs[0].variable
        val resHigh = summaryArgs[1].variable
        return if (resLow !is TACByteStackVariable || resHigh !is TACByteStackVariable) {
            null
        } else {
            Pair(resLow, resHigh)
        }
    }

    /**
     * Summarize compiler-rt functions.
     * Not all functions are currently summarized. Return true if the particular function has a TAC summary.
     **/
    private fun summarizeCompilerRt(locInst: LocatedSbfInstruction,
                                    cmds: MutableList<TACCmd.Simple>): Boolean {
        val inst = locInst.inst
        check(inst is SbfInstruction.Call) {"summarizeCompilerRt expects a call instruction instead of $inst"}

        val function = CompilerRtFunction.from(inst.name) ?: return false
        val (resLow, resHigh) = getLowAndHighFromU128(locInst) ?: return false
        cmds.add(makeDebugExtCallAnnot(inst))
        val xLowE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R2_ARG))
        val xHighE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R3_ARG))
        val yLowE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R4_ARG))
        val yHighE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R5_ARG))

        when (function) {
            CompilerRtFunction.MULTI3, CompilerRtFunction.UDIVTI3  ->  {
                val res = mkFreshIntVar()
                val xE = mergeU128(xLowE, xHighE, cmds)
                val yE = mergeU128(yLowE, yHighE, cmds)
                if (function == CompilerRtFunction.MULTI3) {
                    if (SolanaConfig.UseTACMathInt.get()) {
                        // We are using 256-bits so multiplication of 128-bits cannot overflow
                        val (xMath, yMath, resMath) = Triple(mkFreshMathIntVar(), mkFreshMathIntVar(), mkFreshMathIntVar())
                        cmds.add(promoteToMathInt(xE.asSym(), xMath))
                        cmds.add(promoteToMathInt(yE.asSym(), yMath))
                        cmds.add(mkAssign(resMath, TACExpr.Vec.IntMul(listOf(xMath.asSym(), yMath.asSym()))))
                        cmds.add(narrowFromMathInt(resMath.asSym(), res))
                    } else {
                        cmds.add(mkAssign(res, TACExpr.Vec.Mul(listOf(xE.asSym(), yE.asSym()))))
                    }
                } else {
                    if (SolanaConfig.UseTACMathInt.get()) {
                        // We are using 256-bits so division of 128-bits cannot overflow
                        val (xMath, yMath, resMath) = Triple(mkFreshMathIntVar(), mkFreshMathIntVar(), mkFreshMathIntVar())
                        cmds.add(promoteToMathInt(xE.asSym(), xMath))
                        cmds.add(promoteToMathInt(yE.asSym(), yMath))
                        cmds.add(mkAssign(resMath, TACExpr.BinOp.IntDiv(xMath.asSym(), yMath.asSym())))
                        cmds.add(narrowFromMathInt(resMath.asSym(), res))
                    } else {
                        cmds.add(mkAssign(res, TACExpr.BinOp.Div(xE.asSym(), yE.asSym())))
                    }
                }
                splitU128(res, resLow.tacVar, resHigh.tacVar, cmds)
            }
            CompilerRtFunction.DIVTI3 ->  {
                cmds.add(mkAssign(resLow.tacVar, TACExpr.BinOp.SDiv(xLowE, yLowE)))
                cmds.add(TACCmd.Simple.AssigningCmd.AssignHavocCmd(resHigh.tacVar))
            }
        }
        return true
    }

    /**
     * r1: low(x), r2: high(x), r3: low(y), r4: high(y) and result in r0
     *
     * We do case by case using nested ite terms
     * 1. if high(x) == 0 and high(y) == 0 then low(x) <= low(y)
     * 2. if high(x) == 0 and high(y) != 0 then true
     * 3. if high(x) != 0 and high(y) == 0 then false
     * 4. if high(x) != 0 and high(y) != 0 then (high(x) << 64 + low(x)) <= (high(y) << 64 + low(y))
     **/
    private fun summarizeU128Leq(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        check(inst is SbfInstruction.Call)
        {"summarizeU128Leq expects a call instruction instead of ${locInst.inst}"}
        check(CVTFunction.from(inst.name) == CVTFunction.U128_LEQ)
        {"summarizeU128Leq expects ${CVTFunction.U128_LEQ.function.name}"}

        val cmds = mutableListOf(makeDebugExtCallAnnot(inst))
        val res = exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE)
        val xLowE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R1_ARG))
        val xHighE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R2_ARG))
        val yLowE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R3_ARG))
        val yHighE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R4_ARG))
        val xE = mergeU128(xLowE, xHighE, cmds)
        val yE = mergeU128(yLowE, yHighE, cmds)
        val cond = TACExpr.TernaryExp.Ite(
            TACExpr.BinBoolOp.LAnd(TACExpr.BinRel.Eq(xHighE, TACExpr.zeroExpr),
                TACExpr.BinRel.Eq(yHighE, TACExpr.zeroExpr)),
            exprBuilder.mkBinRelExp(CondOp.LE, xLowE, yLowE),
            TACExpr.TernaryExp.Ite(
                TACExpr.BinBoolOp.LAnd(TACExpr.BinRel.Eq(xHighE, TACExpr.zeroExpr),
                    TACExpr.UnaryExp.LNot(TACExpr.BinRel.Eq(yHighE, TACExpr.zeroExpr))),
                TACSymbol.True.asSym(),
                TACExpr.TernaryExp.Ite(
                    TACExpr.BinBoolOp.LAnd(TACExpr.UnaryExp.LNot(TACExpr.BinRel.Eq(xHighE, TACExpr.zeroExpr)),
                        TACExpr.BinRel.Eq(yHighE, TACExpr.zeroExpr)),
                    TACSymbol.False.asSym(),
                    exprBuilder.mkBinRelExp(CondOp.LE, xE.asSym(), yE.asSym()),
                )
            )
        )
        cmds.add(mkAssign(res, TACExpr.TernaryExp.Ite(cond, exprBuilder.ONE.asSym(), TACExpr.zeroExpr)))
        return cmds
    }

    /**
     *  r1: low(x), r2: high(x) and result in r0
     *
     *  high(x) != 0 || low(x) > 0
     */
    private fun summarizeU128Gt0(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        check(inst is SbfInstruction.Call)
        { "summarizeU128Gt0 expects a call instruction instead of ${locInst.inst}" }
        check(CVTFunction.from(inst.name) == CVTFunction.U128_GT0)
        { "summarizeU128Gt0 expects ${CVTFunction.U128_GT0.function.name}" }

        val cmds = mutableListOf(makeDebugExtCallAnnot(inst))
        val res = exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE)
        val xLowE  = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R1_ARG))
        val xHighE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R2_ARG))
        cmds.add(mkAssign(res, TACExpr.BinBoolOp.LOr(TACExpr.UnaryExp.LNot(TACExpr.BinRel.Eq(xHighE, TACExpr.zeroExpr)),
                                                     exprBuilder.mkBinRelExp(CondOp.GT, xLowE, TACExpr.zeroExpr))))
        return cmds
    }

    /**
     * r2: low(x), r3: high(x), r4: low(y), r5: high(y), low(result) in *(r0+0), and  high(result) in *(r0+8)
     *
     * ceil_div(x, y) = (x + y - 1) / y
     *
     * where x = high(x) << 64 + low(x)
     *       y = high(y) << 64 + low(y)
     */
    private fun summarizeU128CeilDiv(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        check(inst is SbfInstruction.Call)
        { "summarizeU128CeilDiv expects a call instruction instead of ${locInst.inst}" }
        check(CVTFunction.from(inst.name) == CVTFunction.U128_CEIL_DIV)
        { "summarizeU128CeilDiv expects ${CVTFunction.U128_CEIL_DIV.function.name}" }

        val (resLow, resHigh) = getLowAndHighFromU128(locInst) ?: return listOf()
        val xLowE  = exprBuilder.mkVar(SbfRegister.R2_ARG).asSym()
        val xHighE = exprBuilder.mkVar(SbfRegister.R3_ARG).asSym()
        val yLowE  = exprBuilder.mkVar(SbfRegister.R4_ARG).asSym()
        val yHighE = exprBuilder.mkVar(SbfRegister.R5_ARG).asSym()
        val cmds = mutableListOf(makeDebugExtCallAnnot(inst))
        val xE = mergeU128(xLowE, xHighE, cmds)
        val yE = mergeU128(yLowE, yHighE, cmds)
        val res = mkFreshIntVar()
        val (xMath, yMath, resMath) = Triple(mkFreshMathIntVar(), mkFreshMathIntVar(), mkFreshMathIntVar())
        cmds.add(promoteToMathInt(xE.asSym(), xMath))
        cmds.add(promoteToMathInt(yE.asSym(), yMath))
        cmds.add(mkAssign(resMath, TACExpr.BinOp.IntDiv(
            TACExpr.BinOp.IntSub(TACExpr.Vec.IntAdd(xMath.asSym(), yMath.asSym()), exprBuilder.ONE.asSym()),
            yMath.asSym())))
        cmds.add(narrowFromMathInt(resMath.asSym(), res))
        splitU128(res, resLow.tacVar, resHigh.tacVar, cmds)
        return cmds
    }

    /**
     * low(result) in *(r0+0), and  high(result) in *(r0+8)
     *
     * result < 2^128
     *
     * where result = high(result) << 64 + low(result)
     **/
    private fun summarizeU128Nondet(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        check(inst is SbfInstruction.Call)
        { "summarizeU128Nondet expects a call instruction instead of ${locInst.inst}" }
        check(CVTFunction.from(inst.name) == CVTFunction.NONDET_u128)
        { "summarizeU128Nondet expects ${CVTFunction.NONDET_u128.function.name}" }

        val (resLow, resHigh) = getLowAndHighFromU128(locInst) ?: return listOf()
        val res = mkFreshIntVar()
        val cmds = mutableListOf(makeDebugExtCallAnnot(inst))
        cmds.addAll(inRange(res, BigInteger.ZERO,  BigInteger.TWO.pow(128)))
        splitU128(res, resLow.tacVar, resHigh.tacVar, cmds)
        return cmds
    }

    /**
     * Summarize u128 intrinsics.
     **/
    private fun summarizeU128(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        check(inst is SbfInstruction.Call) {"summarizeU128 expects a call instruction instead of ${locInst.inst}"}
        val function = CVTFunction.from(inst.name)
        check(function != null) {"summarizeU128 does not support ${inst.name}"}
        return when (function) {
            CVTFunction.U128_LEQ -> summarizeU128Leq(locInst)
            CVTFunction.U128_GT0 -> summarizeU128Gt0(locInst)
            CVTFunction.U128_CEIL_DIV -> summarizeU128CeilDiv(locInst)
            CVTFunction.NONDET_u128 -> summarizeU128Nondet(locInst)
            else -> {
                throw TACTranslationError("summarizeU128 does not support ${function.name}")
            }
        }
    }

    /**
     * Summarize nativeint intrinsics
     *
     * These intrinsics allow users to write specifications using native integers.
     * Currently, we use 256-bit TAC variables to simulate nativeint.
     */
    private fun summarizeNativeInt(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        check(inst is SbfInstruction.Call) {"summarizeNativeInt expects a call instruction instead of ${locInst.inst}"}
        val function = CVTFunction.from(inst.name)
        check(function != null) {"summarizeNativeInt does not support ${inst.name}"}

        // These symbols are created using 256-bit
        val r1 = exprBuilder.mkVar(SbfRegister.R1_ARG).asSym()
        val r2 = exprBuilder.mkVar(SbfRegister.R2_ARG).asSym()
        val r3 = exprBuilder.mkVar(SbfRegister.R3_ARG).asSym()
        val r4 = exprBuilder.mkVar(SbfRegister.R4_ARG).asSym()
        val r0 = exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE)
        val zero = exprBuilder.ZERO.asSym()
        val one  = exprBuilder.ONE.asSym()

        return listOf(when (function) {
            CVTFunction.NATIVEINT_EQ ->
                mkAssign(r0, TACExpr.TernaryExp.Ite(TACExpr.BinRel.Eq(r1, r2), one, zero))
            CVTFunction.NATIVEINT_LT ->
                mkAssign(r0, TACExpr.TernaryExp.Ite(TACExpr.BinRel.Lt(r1, r2), one, zero))
            CVTFunction.NATIVEINT_LE ->
                mkAssign(r0, TACExpr.TernaryExp.Ite(TACExpr.BinRel.Le(r1, r2), one, zero))
            CVTFunction.NATIVEINT_ADD ->
                mkAssign(r0, TACExpr.Vec.Add(listOf(r1,r2)))
            CVTFunction.NATIVEINT_SUB ->
                mkAssign(r0, TACExpr.BinOp.Sub(r1,r2))
            CVTFunction.NATIVEINT_MUL ->
                mkAssign(r0, TACExpr.Vec.Mul(listOf(r1, r2)))
            CVTFunction.NATIVEINT_DIV ->
                mkAssign(r0, TACExpr.BinOp.Div(r1, r2))
            CVTFunction.NATIVEINT_CEIL_DIV ->
                mkAssign(r0, TACExpr.BinOp.Div(TACExpr.BinOp.Sub(TACExpr.Vec.Add(r1, r2), one), r2))
            CVTFunction.NATIVEINT_MULDIV ->
                mkAssign(r0, TACExpr.BinOp.Div(TACExpr.Vec.Mul(r1, r2), r3))
            CVTFunction.NATIVEINT_MULDIV_CEIL ->
                mkAssign(r0, TACExpr.BinOp.Div(TACExpr.BinOp.Sub(TACExpr.Vec.Add(TACExpr.Vec.Mul(r1, r2), r3), one), r3))
            CVTFunction.NATIVEINT_NONDET ->
                TACCmd.Simple.AssigningCmd.AssignHavocCmd(r0)
            CVTFunction.NATIVEINT_FROM_u128 -> /* build a nativeint from u128 (two 64-bit registers) */
                mergeU128(r0, r1, r2)
            CVTFunction.NATIVEINT_FROM_u256 -> /* build a nativeint from u256 (four 64-bit registers) */
                mergeU256(r0, r1, r2, r3, r4)
            CVTFunction.NATIVEINT_u64_MAX ->
                mkAssign(r0, (BigInteger.TWO.pow(64) - BigInteger.ONE).asTACExpr())
            CVTFunction.NATIVEINT_u128_MAX ->
                mkAssign(r0, (BigInteger.TWO.pow(128) - BigInteger.ONE).asTACExpr())
            CVTFunction.NATIVEINT_u256_MAX ->
                mkAssign(r0, (BigInteger.TWO.pow(256) - BigInteger.ONE).asTACExpr())
            else ->
                throw TACTranslationError("summarizeNativeInt does not expect ${function.name}")
        })
    }

    /**
     * `cvt_alloc_slice(base:ptr, offset:usize, size:usize) -> ptr`
     *
     *  Preconditions:
     *   1) `base` is the base of some allocated object `X`
     *   2) the size of object `X` must be greater than `offset` + `size`.
     *
     *  Return a pointer that points to a fresh allocated object of size `size` whose address is `base` + `offset`
     *
     *  **IMPORTANT**: we cannot check the preconditions at the TAC level so they must be ensured when calling CVT_alloc_slice
     **/
    private fun summarizeAllocSlice(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        check(inst is SbfInstruction.Call)
        val offset = (regTypes.typeAtInstruction(locInst, SbfRegister.R2_ARG) as? SbfType.NumType)?.value?.get()
            ?: throw TACTranslationError("Cannot statically infer the offset (r2) in $locInst")
        if (offset < 0) {
            throw TACTranslationError("$locInst does not support negative offsets (r2) but given $offset")
        }
        val cmds = mutableListOf(makeDebugExtCallAnnot(inst))
        val baseE = exprBuilder.mkVar(SbfRegister.R1_ARG).asSym()
        val offsetE = exprBuilder.mkConst(Value.Imm(offset.toULong())).asSym()
        val lhsE = exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE)
        if (SolanaConfig.UseTACMathInt.get()) {
            val x = mkFreshMathIntVar()
            val y = mkFreshMathIntVar()
            val z = mkFreshMathIntVar()
            cmds.add(promoteToMathInt(baseE, x))
            cmds.add(promoteToMathInt(offsetE, y))
            cmds.add(mkAssign(z, exprBuilder.mkBinExpr(BinOp.ADD, x.asSym(), y.asSym(), useMathInt = true)))
            cmds.add(narrowFromMathInt(z.asSym(), lhsE))
        } else {
            val rhs = exprBuilder.mkBinExpr(BinOp.ADD, baseE, offsetE, useMathInt = false)
            cmds.add(mkAssign(lhsE, rhs))
        }
        cmds.add(makeCallTraceExtCall(inst, listOf(exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE))))
        return cmds
    }

    private fun summarizeCall(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        check(inst is SbfInstruction.Call) { "summarizeCall expects only call instructions" }

        val cmds = mutableListOf<TACCmd.Simple>()

        if (summarizeCompilerRt(locInst, cmds)) {
            return cmds
        }

        cmds.add(makeDebugExtCallAnnot(inst))
        val summaryArgs = mem.getTACMemoryFromSummary(locInst) ?: listOf()
        if (summaryArgs.isNotEmpty()) {
            for ((i, arg) in summaryArgs.withIndex()) {
                val (tacV, useAssume) =  when (val v = arg.variable) {
                    is TACByteStackVariable -> {
                        Pair(v.tacVar, false)
                    }
                    is TACByteMapVariable -> {
                        val lhs = mkFreshIntVar()
                        val loc = computeTACMapIndex(exprBuilder.mkVar(arg.reg), arg.offset, cmds)
                        cmds.add(TACCmd.Simple.AssigningCmd.ByteLoad(lhs, loc, v.tacVar))
                        Pair(lhs, true)
                    }
                }

                when (arg.type) {
                    MemSummaryArgumentType.PTR_HEAP -> {
                        val allocatedSize = if (arg.allocatedSpace > 0UL) {
                            arg.allocatedSpace
                        } else {
                            val defaultSize = SolanaConfig.TACHeapAllocSize.get().toULong()
                            sbfLogger.warn { "TAC allocation of unknown size: fixing $defaultSize bytes for $i-th parameter at $locInst" }
                            defaultSize
                        }
                        // let's assume this summary for foo
                        //  ```
                        //  #[type((*i64)(r1+0):ptr_external(1024))]
                        //  #[type((*i64)(r1+8):ptr_external(1024))]
                        //
                        //   r1 = r10[-200]
                        //   "foo"()
                        //   r2 = r1[0]
                        //   r3 = r1[8]
                        //  ```
                        //  The call to `foo` will add some TAC like this
                        //  ```
                        //   let x := ByteLoad(M, r1)
                        //   let y := ByteLoad(M, r1+8)
                        //   x := some fixed address
                        //   y := x + 1024
                        //  ```
                        //  As a result `r2 = r1[0]` won't know that `r2` should be x.
                        //  If the 3rd parameter of `alloc` (see below) is true then the TAC will be like this
                        //   ```
                        //   let x = ByteLoad(M, r1)
                        //   let y = ByteLoad(M, r1+8)
                        //   assume(x == some fixed address) // this propagates back to M
                        //   assume(y == x + 1024)           // this propagates back to M
                        //   ```
                        cmds.addAll(heapMemAlloc.alloc(tacV, allocatedSize, useAssume))
                    }
                    MemSummaryArgumentType.PTR_EXTERNAL -> {
                        val allocatedSize = if (arg.allocatedSpace > 0UL) {
                            arg.allocatedSpace
                        } else {
                            val defaultSize = SolanaConfig.TACExternalAllocSize.get().toULong()
                            sbfLogger.warn { "TAC allocation of unknown size: fixing $defaultSize bytes for $i-th parameter at $locInst" }
                            defaultSize
                        }
                        cmds.addAll(extMemAlloc.alloc(tacV, allocatedSize, useAssume))
                    }
                    else -> {
                        cmds.add(TACCmd.Simple.AssigningCmd.AssignHavocCmd(tacV))
                    }
                }

            }
        }
        cmds.add(TACCmd.Simple.AssigningCmd.AssignHavocCmd(exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE)))
        if (memoryAnalysis?.memSummaries?.getSummary(inst.name) == null) {
            unsupportedCalls.add(inst.name)
        }
        return cmds
    }

    private fun translateCall(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        check(inst is SbfInstruction.Call) {"TAC translateCall expects a call instead of $inst"}
        if (inst.isAbort()) {
            // If the abort was added by the slicer then we skip it in TAC because it can cause problems to sanity rules
            return if (inst.metaData.getVal(SbfMeta.UNREACHABLE_FROM_COI) != null) {
                listOf()
            } else {
                makeUnreachable(inst)
            }
        } else if (inst.isAllocFn()) {
            val size = (regTypes.typeAtInstruction(locInst, SbfRegister.R1_ARG) as? SbfType.NumType)?.value?.get()
            val sizeOrDefault = if (size != null) {
                size
            } else {
                val defaultSize = SolanaConfig.TACHeapAllocSize.get().toLong()
                sbfLogger.warn{ "TAC allocation of unknown size: fixing $defaultSize bytes at $locInst"}
                defaultSize
            }
            if (sizeOrDefault <= 0) {
                throw TACTranslationError("${heapMemAlloc.name}::alloc expects non-zero, positive sizes")
            }
            return listOf(makeDebugExtCallAnnot(inst)) +
                   heapMemAlloc.alloc(exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE), sizeOrDefault.toULong()) +
                   listOf(makeCallTraceExtCall(inst, listOf(exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE))))
        } else {
            val cvtFunction = CVTFunction.from(inst.name)
            if (cvtFunction != null) {
                when (cvtFunction) {
                    CVTFunction.ASSUME, CVTFunction.ASSERT -> {
                        throw TACTranslationError("unsupported call to ${inst.name}. " +
                                                  "SimplifyBuiltinCalls::renameCVTCall was probably not called.")
                    }
                    CVTFunction.SANITY -> {
                        return translateSanity(inst)
                    }
                    CVTFunction.SATISFY -> {
                        return translateSatisfy(inst)
                    }
                    CVTFunction.NONDET_i8, CVTFunction.NONDET_i16, CVTFunction.NONDET_i32, CVTFunction.NONDET_i64 -> {
                        val r0 = exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE)
                        val n = when (cvtFunction) {
                            CVTFunction.NONDET_i8  -> BigInteger.TWO.pow(8-1)
                            CVTFunction.NONDET_i16 -> BigInteger.TWO.pow(16-1)
                            CVTFunction.NONDET_i32 -> BigInteger.TWO.pow(32-1)
                            CVTFunction.NONDET_i64 -> BigInteger.TWO.pow(64-1)
                            else -> {
                                // compiler is not smart enough
                                throw TACTranslationError("Unexpected CVT_nondet signed integer function ${inst.name}")
                            }
                        }
                        return  listOf(makeDebugExtCallAnnot(inst), TACCmd.Simple.AssigningCmd.AssignHavocCmd(r0)) +
                                inRange(r0, -n, n, false) +
                                listOf(makeCallTraceExtCall(inst, listOf(r0)))
                    }
                    CVTFunction.NONDET_u8, CVTFunction.NONDET_u16, CVTFunction.NONDET_u32, CVTFunction.NONDET_u64, CVTFunction.NONDET_usize -> {
                        val r0 = exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE)
                        val n = when (cvtFunction) {
                            CVTFunction.NONDET_u8  -> BigInteger.TWO.pow(8)
                            CVTFunction.NONDET_u16 -> BigInteger.TWO.pow(16)
                            CVTFunction.NONDET_u32 -> BigInteger.TWO.pow(32)
                            CVTFunction.NONDET_u64, CVTFunction.NONDET_usize -> {
                                /// usize is the size of a pointer
                                BigInteger.TWO.pow(64)
                            }
                            else -> {
                                // compiler is not smart enough
                                throw TACTranslationError("Unexpected CVT_nondet unsigned integer function ${inst.name}")
                            }
                        }
                        return listOf(makeDebugExtCallAnnot(inst), TACCmd.Simple.AssigningCmd.AssignHavocCmd(r0)) +
                               inRange(r0, BigInteger.ZERO, n) +
                               makeCallTraceExtCall(inst, listOf(r0))
                    }
                    CVTFunction.SAVE_SCRATCH_REGISTERS -> {
                        val v6 = mkFreshIntVar(prefix = "saved_r6")
                        val v7 = mkFreshIntVar(prefix = "saved_r7")
                        val v8 = mkFreshIntVar(prefix = "saved_r8")
                        val v9 = mkFreshIntVar(prefix = "saved_r9")
                        scratchRegVars.add(v6)
                        scratchRegVars.add(v7)
                        scratchRegVars.add(v8)
                        scratchRegVars.add(v9)
                        val startInlineAnnot = inst.toStartInlinedAnnotation(locInst)?.let {
                            listOf(TACCmd.Simple.AnnotationCmd(
                                TACCmd.Simple.AnnotationCmd.Annotation(SBF_INLINED_FUNCTION_START, it))
                            )
                        } ?: listOf()
                        return startInlineAnnot + listOf(
                            mkAssign(v6, TACExpr.Sym.Var(exprBuilder.mkVar(SbfRegister.R6))),
                            mkAssign(v7, TACExpr.Sym.Var(exprBuilder.mkVar(SbfRegister.R7))),
                            mkAssign(v8, TACExpr.Sym.Var(exprBuilder.mkVar(SbfRegister.R8))),
                            mkAssign(v9, TACExpr.Sym.Var(exprBuilder.mkVar(SbfRegister.R9))))
                    }
                    CVTFunction.RESTORE_SCRATCH_REGISTERS -> {
                        if (scratchRegVars.size < 4) {
                            throw TACTranslationError("number of save/restore does not match")
                        }
                        val v9 = scratchRegVars.removeLast()
                        val v8 = scratchRegVars.removeLast()
                        val v7 = scratchRegVars.removeLast()
                        val v6 = scratchRegVars.removeLast()
                        val endInlineAnnot = inst.toEndInlineAnnotation()?.let {
                            listOf(TACCmd.Simple.AnnotationCmd(
                                TACCmd.Simple.AnnotationCmd.Annotation(SBF_INLINED_FUNCTION_END, it))
                            )
                        } ?: listOf()
                        return endInlineAnnot + listOf(
                            mkAssign(exprBuilder.mkVar(SbfRegister.R6), TACExpr.Sym.Var(v6)),
                            mkAssign(exprBuilder.mkVar(SbfRegister.R7), TACExpr.Sym.Var(v7)),
                            mkAssign(exprBuilder.mkVar(SbfRegister.R8), TACExpr.Sym.Var(v8)),
                            mkAssign(exprBuilder.mkVar(SbfRegister.R9), TACExpr.Sym.Var(v9)))
                    }
                    CVTFunction.CEX_PRINT_i64_1, CVTFunction.CEX_PRINT_i64_2, CVTFunction.CEX_PRINT_i64_3,
                    CVTFunction.CEX_PRINT_TAG,
                    CVTFunction.CEX_PRINT_u64_1, CVTFunction.CEX_PRINT_u64_2, CVTFunction.CEX_PRINT_u64_3 -> {
                        return listOf(makeCallTraceCexValOrTag(locInst, cvtFunction))
                    }
                    CVTFunction.CEX_PRINT_LOCATION -> {
                        return listOf(makeCallTraceCexPrintLocation(locInst))
                    }
                    CVTFunction.CEX_ATTACH_LOCATION -> {
                        return listOf(makeCallTraceCexAttachLocation(locInst))
                    }
                    CVTFunction.CEX_PRINT_STRING -> {
                        return listOf(makeCallTraceCexString(locInst))
                    }
                    CVTFunction.NONDET_u128, CVTFunction.U128_GT0, CVTFunction.U128_LEQ, CVTFunction.U128_CEIL_DIV -> {
                        return if (SolanaConfig.UseTACMathInt.get()) {
                            summarizeU128(locInst)
                        } else {
                            summarizeCall(locInst)
                        }
                    }
                    CVTFunction.NATIVEINT_EQ, CVTFunction.NATIVEINT_LT, CVTFunction.NATIVEINT_LE,
                    CVTFunction.NATIVEINT_ADD, CVTFunction.NATIVEINT_SUB, CVTFunction.NATIVEINT_MUL,
                    CVTFunction.NATIVEINT_DIV, CVTFunction.NATIVEINT_CEIL_DIV,
                    CVTFunction.NATIVEINT_MULDIV, CVTFunction.NATIVEINT_MULDIV_CEIL,
                    CVTFunction.NATIVEINT_NONDET,
                    CVTFunction.NATIVEINT_FROM_u128, CVTFunction.NATIVEINT_FROM_u256,
                    CVTFunction.NATIVEINT_u64_MAX, CVTFunction.NATIVEINT_u128_MAX, CVTFunction.NATIVEINT_u256_MAX -> {
                        return summarizeNativeInt(locInst)
                    }
                    CVTFunction.NONDET_ACCOUNT_INFO -> {
                        if (!SolanaConfig.CvtNondetAccountInfo.get()) {
                            /**
                            * IMPORTANT: we don't treat this function as a summarized function for which we would do
                            * symbolic allocation at the TAC level because this function is already precisely modeled at the
                            * Rust level.
                            */
                            return listOf(makeDebugExtCallAnnot(inst))
                        }
                        // else skip on purpose. The function will be treated as regular summarized function.
                    }
                    CVTFunction.NONDET_SOLANA_ACCOUNT_SPACE -> {
                        val size = (regTypes.typeAtInstruction(locInst, SbfRegister.R1_ARG) as? SbfType.NumType)?.value?.get()
                            ?: throw TACTranslationError("Cannot statically infer the size in $locInst")
                        return listOf(makeDebugExtCallAnnot(inst)) +
                               accountsAlloc.alloc(exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE), size) +
                               listOf(makeCallTraceExtCall(inst, listOf(exprBuilder.mkVar(SbfRegister.R0_RETURN_VALUE))))
                    }
                    CVTFunction.ALLOC_SLICE -> {
                        return summarizeAllocSlice(locInst)
                    }
                }
            }

            val solFunction  = SolanaFunction.from(inst.name)
            if (solFunction != null) {
                when (solFunction) {
                    SolanaFunction.SOL_MEMCPY -> {
                        return translateMemCopy(locInst)
                    }
                    SolanaFunction.SOL_MEMCMP -> {
                        return translateMemCompare(locInst)
                    }
                    SolanaFunction.SOL_MEMSET -> {
                        return translateMemSet(locInst)
                    }
                    else -> { /* handled below */ }
                }
            }

            return summarizeCall(locInst)
        }
    }

    private fun translateMem(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        check(inst is SbfInstruction.Mem) {"TAC translateMem expects memory instruction instead of $inst"}
       //val locInst = LocatedSbfInstruction(bb.getLabel(), SbfInstructionAsRef(inst))
        val loadOrStore = mem.getTACMemory(locInst)
        return if (loadOrStore == null) {
            /* The instruction is unreachable */
            makeUnreachable(inst)
        } else {
            val memVar = loadOrStore.variable
            val newCmds = mutableListOf<TACCmd.Simple>()
            if (memVar is TACByteStackVariable) {
                /* scalar variable */
                if (inst.isLoad) {
                    val lhs = exprBuilder.mkVar((inst.value as Value.Reg).r)
                    newCmds.add(mkAssign(lhs, memVar.tacVar.asSym()))
                } else {
                    if (SolanaConfig.UsePTA.get()) {
                        // havoc any possible overlaps
                        val scalarsToHavoc = loadOrStore.locationsToHavoc
                        check(scalarsToHavoc is TACMemSplitter.HavocScalars) { "TAC translateMem expects HavocScalars" }
                        havocScalars(scalarsToHavoc.vars.map { it.tacVar }, newCmds)
                    }
                    newCmds.add(mkAssign(memVar.tacVar, exprBuilder.mkExprSym(inst.value)))
                }
            } else {
                /* byte map variable */
                check(memVar is TACByteMapVariable) {"TAC translateMem expects a byte map variable"}
                val baseReg = inst.access.baseReg
                val offset = inst.access.offset
                val loc = computeTACMapIndex(exprBuilder.mkVar(baseReg), offset.toLong(), newCmds)
                if (inst.isLoad) {
                    val lhs = exprBuilder.mkVar((inst.value as Value.Reg).r)
                    newCmds.add(TACCmd.Simple.AssigningCmd.ByteLoad(lhs, loc, memVar.tacVar))
                } else {
                    if (SolanaConfig.UsePTA.get()) {
                        // havoc any possible overlaps
                        val mapFieldsToHavoc = loadOrStore.locationsToHavoc
                        check(mapFieldsToHavoc is TACMemSplitter.HavocMapBytes) { "TAC translateMem expects HavocMapBytes" }
                        havocByteMapLocation(mapFieldsToHavoc.fields, memVar, loc, newCmds)
                    }
                    val value = when (inst.value) {
                            is Value.Imm -> { exprBuilder.mkConst(inst.value) }
                            is Value.Reg -> { exprBuilder.mkVar(inst.value) }
                    }
                    newCmds.add(TACCmd.Simple.AssigningCmd.ByteStore(loc, value, memVar.tacVar))
                }
                val baseRegType = regTypes.typeAtInstruction(locInst, baseReg.r)
                newCmds.addAll(addMemoryLayoutAssumptions(loc, baseRegType))
            }
            newCmds
        }
    }

    private fun addSbfAddressAsMeta(stmts: List<TACCmd.Simple>, locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val address = locInst.inst.metaData.getVal(SbfMeta.SBF_ADDRESS)
        return if (address != null){
            check(address <= Long.MAX_VALUE.toULong()) {"Address $address is too big SVM"}
            stmts.map {
                val newMeta = it.meta.add(Pair(SBF_ADDRESS, address.toLong()))
                it.withMeta(newMeta)
            }
        } else {
            stmts
        }
    }

    private fun translate(locInst: LocatedSbfInstruction): List<TACCmd.Simple> {
        val inst = locInst.inst
        sbfLogger.debug {"\tTAC translation of $inst"}
        val stmts = when (inst) {
            is SbfInstruction.Mem -> translateMem(locInst)
            is SbfInstruction.Bin -> translateBin(inst, useMathInt = false)
            is SbfInstruction.Un -> translateUn(inst)
            is SbfInstruction.Jump -> translateJump(locInst)
            is SbfInstruction.Havoc -> translateHavoc(inst)
            is SbfInstruction.Select -> translateSelect(inst)
            is SbfInstruction.Assert -> translateAssert(locInst)
            is SbfInstruction.Assume -> translateAssume(locInst)
            is SbfInstruction.Call -> translateCall(locInst)
            is SbfInstruction.Exit -> translateExit()
            is SbfInstruction.CallReg -> {
                if (!SolanaConfig.SkipCallRegInst.get()) {
                    throw TACTranslationError("unsupported $inst")
                } else {
                    listOf()
                }
            }
        }
        return addSbfAddressAsMeta(stmts, locInst)
    }

    private fun translate(bb: SbfBasicBlock): List<TACCmd.Simple> {
        check(cfg.getBlock(bb.getLabel()) != null){"Basic block ${bb.getLabel()} not found in CFG ${cfg.getName()}"}
        check(bb.getInstructions().isNotEmpty()){"A SbfBasicBlock should not be empty"}
        sbfLogger.debug {"TAC translation of block ${bb.getLabel()}"}
        val cmds: MutableList<TACCmd.Simple> = mutableListOf()
        for (locInst in bb.getLocatedInstructions()) {
            cmds.addAll(translate(locInst))
        }
        check(cmds.isNotEmpty()){"A TAC basic block should not be empty "}
        return cmds
    }

    // For debugging
    private fun dumpTAC(program: CoreTACProgram): String {
        val sb = StringBuilder()
        program.code.forEachEntry { (id, commands) ->
            sb.append("Block $id:\n")
            commands.forEach { command ->
                sb.append("\t${command}\n")
            }
        }
        sb.append("Graph\n")
        program.blockgraph.forEachEntry { (u, vs) ->
            sb.append("$u -> ${vs.joinToString(" ")}\n")
        }
        return sb.toString()
    }

    // Convert a CFG to a TACProgram
    fun encode(): CoreTACProgram {
        val entry = cfg.getEntry()
        // It is important for the rest of the pipeline that the entry block is assigned 0
        mkBlockIdentifier(entry)
        cfg.getBlocks().values.forEach {
            if (it != entry) {
                mkBlockIdentifier(it)
            }
        }

        // We need to traverse in depth-first search in order to encode correctly
        // __CVT_restore_scratch_registers.
        val worklist = ArrayList<SbfBasicBlock>()
        val visited: MutableSet<Label> = mutableSetOf(entry.getLabel())
        worklist.add(entry)
        while (worklist.isNotEmpty()) {
            val block = worklist.removeLast()
            val tacBB = getBlockIdentifier(block)
            if (isEntryPoint && entry.getLabel() == block.getLabel()) {
                val cmds = ArrayList<TACCmd.Simple>()
                cmds.addAll(addInitialPreconditions())
                cmds.addAll(translate(block))
                code[tacBB] = cmds
            } else {
                val cmds = translate(block)
                check(cmds.isNotEmpty()) {"TAC block $tacBB is empty. Original block is $block"}
                code[tacBB] = cmds
            }
            for (succ in block.getSuccs()) {
                val succTacBB = getBlockIdentifier(succ)
                blockGraph[tacBB] = blockGraph[tacBB].orEmpty() + succTacBB
                if (visited.add(succ.getLabel())) {
                    worklist.add(succ)
                }
            }
        }

        // Prune unreachable blocks
        // We shouldn't have unreachable blocks at this point, except if the exit of the CFG is unreachable.
        // This is because our CFG normalization adds one even if it's unreachable.
        for (block in cfg.getBlocks().values) {
            if (!visited.contains(block.getLabel())) {
                removeBlockIdentifier(block.getLabel())
            }
        }

        // Initialize all TAC variables non-deterministically
        // We also initialize unnecessarily TAC registers used to save SBF scratch registers
        val tacEntryB = getBlockIdentifier(entry)
        val initCmds = mutableListOf<TACCmd.Simple>()
        declaredVars.addAll(vFac.getDeclaredVariables())
        for (v in declaredVars) {
            initCmds.add(TACCmd.Simple.AssigningCmd.AssignHavocCmd(v))
        }
        val entryCmds = code[tacEntryB]
        check(entryCmds != null) {"cannot find TAC code for the entry block"}
        code[tacEntryB] = initCmds + entryCmds

        val symbolTable = TACSymbolTable(declaredVars.toSet())
        val name = cfg.getName()
        val procs = mutableSetOf<Procedure>() // this is used by CEX generation
        val program = CoreTACProgram(code, blockGraph, name, symbolTable, procs,
                                    true, entryBlock = getBlockIdentifier(entry))

        if (unsupportedCalls.isNotEmpty()) {
            val sb = StringBuilder()
            sb.append("TAC encoding of the following external calls might be unsound because " +
                      "only the output has been havoced\n")
            for (e in unsupportedCalls) {
                sb.append("\t$e\n")
            }
            sbfLogger.warn { sb.toString() }
        }

        if (SolanaConfig.PrintTACToStdOut.get()) {
            sbfLogger.info {"------- TAC program --------\n" + dumpTAC(program)}
        }
        return program
    }
}
