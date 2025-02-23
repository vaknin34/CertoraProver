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

package sbf.callgraph

import datastructures.stdcollections.*
import sbf.SolanaConfig
import sbf.cfg.*
import sbf.disassembler.*
import sbf.sbfLogger
import sbf.support.demangle

/**
 * Conversion of an SbfProgram (i.e., a sequence of labeled sbf instructions)
 * to a list of CFGs.
 **/
fun sbfProgramToSbfCfgs(prog: SbfProgram): MutableSbfCallGraph {
    /**
     * We first build a big monolithic CFG representing the whole sbf program.
     * Since an sbf program can have multiple functions,
     * @monoCFG is actually a set of disconnected CFGs (one per function).
     * Note that @monoCFG will be thrown away later, so it won't survive beyond this function.
     **/
    val monoCFG = MutableSbfCFG("mono_cfg")
    val functions = mutableSetOf<Pair<String, ElfAddress>>()
    prog.entriesMap.forEachEntry {
        functions.add(it.key to it.value)
    }

    val targets = MutableSbfCFG.getTargets(prog)
    var curBlock: MutableSbfBasicBlock? = null
    var exitDominates = false
    prog.program.forEachIndexed lit@{ i, labeledInst ->
        val pc = labeledInst.first
        val inst = labeledInst.second
        val prevBlock = curBlock

        if (targets.contains(pc) || (curBlock != null && curBlock!!.getInstruction(curBlock!!.numOfInstructions() - 1) is SbfInstruction.Jump)) {
            /*The second condition ensures that we don't have two goto instructions in the same block.
            * This seems to happen when LLVM invoke instructions are lowered.
            * The LLVM code:
            *   invoke void @core::result::unwrap_failed(....)
            *   to label %normal unwind label %cleanup,
            * normal:
            *   unreachable
            * bb4:
            *   br label %bb5
            * cleanup:
            *  %18 = landingpad { i8*, i32 } cleanup
            *  ...
            *  br label %bb4
            * bb5: ...
            *
            * into sbf code:
            *
            * 1200:	call core::result::unwrap_failed
            * 1201:	goto 1202
            * 1202:
            *      goto 1208 // first goto
            *      r1 := *(u64 *) (r10 + -160) <- DEAD
            *      r2 := *(u64 *) (r10 + -168) <- DEAD
            *      *(u64 *) (r10 + -32) := r2  <- DEAD
            *      *(u32 *) (r10 + -24) := r1  <- DEAD
            *      goto 1202 // second goto: we don't allow two goto's in the same block.
            */
            curBlock = monoCFG.getOrInsertBlock(pc)
            // The dominance of exit terminates here
            exitDominates = false
        }

        if (curBlock == null) {
            throw CFGBuilderError("couldn't get a basic block for label $pc")
        }

        curBlock?.let {
            if (exitDominates) {
                // skip the instruction because it's dead (it's dominated by an exit instruction)
                return@lit // this has the effect of continue
            }

            if (prevBlock != null && prevBlock.getLabel() != it.getLabel()) {
                val lastInstPrevBlock = prevBlock.getInstruction(prevBlock.numOfInstructions() - 1)
                if (lastInstPrevBlock !is SbfInstruction.Jump && lastInstPrevBlock !is SbfInstruction.Exit) {
                    prevBlock.add(SbfInstruction.Jump.UnconditionalJump(pc))
                    prevBlock.addSucc(it)
                }
            }

            if (inst is SbfInstruction.Call) {
                val funcStart = inst.entryPoint
                if (funcStart != null) {
                    val funcName = prog.funcMan.getFunction(funcStart)?.name
                        ?: throw CFGBuilderError("cannot find a name for a function starting at address $funcStart")
                    functions.add(funcName to funcStart)
                }
            }

            when (inst) {
                is SbfInstruction.Exit -> {
                    it.add(inst)
                    exitDominates = true
                }
                is SbfInstruction.Jump.UnconditionalJump -> {
                    val succBlock = monoCFG.getOrInsertBlock(inst.target)
                    it.addSucc(succBlock)
                    it.add(inst)
                }
                is SbfInstruction.Jump.ConditionalJump -> {
                    if (i + 1 >= prog.program.size) {
                        throw CFGBuilderError("out-of-bounds jump instruction")
                    }
                    val nextPC = prog.program[i + 1].first
                    val jumpCondInst = SbfInstruction.Jump.ConditionalJump(inst.cond, inst.target, nextPC)
                    val trueSuccBlock = monoCFG.getOrInsertBlock(inst.target)
                    val falseSuccBlock = monoCFG.getOrInsertBlock(nextPC)

                    if (trueSuccBlock.getLabel() == falseSuccBlock.getLabel()) {
                        // It's possible to have useless conditional jump.
                        //      934:	2d 67 00 00 00 00 00 00	if r7 > r6 goto +0 <LBB2_94>
                        //0000000000001d38 LBB2_94:
                        //      935:	...
                        it.add(SbfInstruction.Jump.UnconditionalJump(inst.target))
                        it.addSucc(trueSuccBlock)
                    } else {
                        it.add(jumpCondInst)
                        it.addSucc(trueSuccBlock)
                        it.addSucc(falseSuccBlock)
                    }
                }
                else -> {
                    it.add(inst)
                }
            }
        }
    }

    /***
     * At this point, we split monoCFG into multiple CFGs (one per function)
     * We know the start address of each function.
     * Each CFG consists of all reachable blocks from each start.
     * We rename basic block labels to avoid any possible clash.
     */
    val labelMap = monoCFG.renameLabels() //needed by postProcessCFG
    val cfgs = ArrayList<MutableSbfCFG>()
    for ((name, start) in functions) {
        val labeledStart = labelMap[Label.Address(start)]
        check(labeledStart != null) { "found a label in the label map" }
        val entryBlock = monoCFG.getBlock(labeledStart)
            ?: throw CFGBuilderError("cannot find basic block for function=${name} at entry block=$start")
        val cfg = monoCFG.sliceFrom(entryBlock.getLabel(), name)
        val clonedCfg = cfg.clone(cfg.getName())
        if (SolanaConfig.PrintOriginalToStdOut.get()) {
            sbfLogger.info { "$clonedCfg" }
        }
        postProcessCFG(clonedCfg, prog.globalsMap)
        cfgs.add(clonedCfg)
    }
    val roots = prog.entriesMap.map { it.key }.toSet()
    return MutableSbfCallGraph(demangle(cfgs).toMutableList(), roots, prog.globalsMap)
}

private fun postProcessCFG(cfg: MutableSbfCFG, globalsMap: GlobalVariableMap) {
    cfg.verify(false, "[before postProcessCFG]")
    //do not call simplify before calling lowerBranchesIntoAssume
    cfg.lowerBranchesIntoAssume()
    cfg.verify(false, "[after lowering branches into assumes]")
    //do not call simplify before calling simplifyMemoryIntrinsics
    simplifyMemoryIntrinsics(cfg)
    cfg.verify(false, "[after simplifying builtin calls]")
    cfg.simplify(globalsMap)
    cfg.verify(false, "[after simplify]")
    markAddWithOverflow(cfg)
    cfg.verify(false, "[after markAddWithOverflow]")
    cfg.normalize()
    cfg.verify(true, "[after normalize]")
}

private fun demangle(cfgs: List<MutableSbfCFG>): List<MutableSbfCFG> {

    /** Make inMap an injective function
     *
     *  Before we demangle, we can have two different function names foo\#123456 and foo\#848474 where
     *  \#123456 and \#848474 are hashes generated by the compiler.
     *  Since we ignore hashes when we demangle names, inMap = { foo\#123456 -> foo, foo\#848474 -> foo}.
     *  After the execution of makeInjective inMap = { foo\#123456 -> foo_1, foo\#848474 -> foo_2}
     **/
    fun makeInjective(inMap: MutableMap<String, String>) {
        val invMap: MutableMap<String, ArrayList<String>> = mutableMapOf()
        for (kv in inMap) {
            val x = invMap[kv.value]
            if (x == null) {
                invMap[kv.value] = arrayListOf(kv.key)
            } else {
                x.add(kv.key)
                invMap[kv.value] = x
            }
        }
        for (kv in invMap) {
            val domainVals = kv.value
            if (domainVals.size > 1) {
                for ((i, domainVal) in domainVals.withIndex()) {
                    val codomainVal = inMap[domainVal]
                    inMap[domainVal] = "${codomainVal}_$i"
                }
            }
        }
    }

    fun buildDemanglerMap(): Map<String, String>? {
        // Collect all function and calls names
        val mangledNames = mutableSetOf<String>()
        for (cfg in cfgs) {
            mangledNames.add(cfg.getName())
            for (block in cfg.getBlocks().values) {
                for (inst in block.getInstructions()) {
                    if (inst is SbfInstruction.Call) {
                        mangledNames.add(inst.name)
                    }
                }
            }
        }
        val mangledNamesList = mangledNames.toList()
        val demangledNames = demangle(mangledNamesList) // call rustfilt to demangle names
        return if (demangledNames == null || demangledNames.size != mangledNamesList.size) {
            // here if the call to rustfilt fails for some reason
            null
        } else {
            val remap: MutableMap<String, String> = mutableMapOf()
            mangledNamesList.forEachIndexed { i, mangledName ->
                remap[mangledName] = demangledNames[i]
            }
            makeInjective(remap)
            remap
        }
    }

    val demanglingMap = buildDemanglerMap()
    if (demanglingMap == null) {
        return cfgs
    } else {
        val demangledCFGs = ArrayList<MutableSbfCFG>(cfgs.size)
        for (cfg in cfgs) {
            val demangledCFG = cfg.clone(demanglingMap.getOrDefault(cfg.getName(), cfg.getName()))
            for (block in demangledCFG.getMutableBlocks().values) {
                var i = 0
                while (i < block.getInstructions().size) {
                    val inst = block.getInstruction(i)
                    if (inst is SbfInstruction.Call) {
                        block.replaceInstruction(i, inst.copy(name = demanglingMap.getOrDefault(inst.name, inst.name)))
                    }
                    i++
                }
            }
            demangledCFGs.add(demangledCFG)
        }
        return demangledCFGs
    }
}

