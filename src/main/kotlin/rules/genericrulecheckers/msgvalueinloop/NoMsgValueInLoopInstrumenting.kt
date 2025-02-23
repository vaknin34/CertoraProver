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

package rules.genericrulecheckers.msgvalueinloop

import datastructures.stdcollections.*
import analysis.*
import analysis.CommandWithRequiredDecls.Companion.withDecls
import analysis.worklist.StepResult
import analysis.worklist.VisitingWorklistIteration
import log.*
import scene.IScene
import tac.MetaMap
import tac.Tag
import utils.*
import vc.data.*
import vc.data.tacexprutil.TACExprFactSimple
import vc.data.tacexprutil.TACExprFreeVarsCollector
import java.math.BigInteger

private val logger = Logger(LoggerTypes.GENERIC_RULE)

/**
 * The class adds instrumentation for finding uses of msg.value in loops and for delegate calls.
 * Special variables are generated in order to track transitive uses of msg.value and to get smt reachability
 * analysis and not rely only on static analysis.
 * After each use node of msg.value y = f(msg.value) add:
 * if the reference is direct y_msgvalueref=true. where y_msgvalueref is a new variable indicating y is a reference to
 * msg.value.
 * Otherwise if y = f(x_1,.., x_n) y = LOR_{x_i refers to msg.value}  x_i_msgvalueref
 * When inside a loop: add error_var LOR_{x refers to msg.value}  x_i_msgvalueref
 */
class NoMsgValueInLoopInstrumenting(val scene: IScene, val tacProgram: CoreTACProgram) {

    private val monitorVarName = "msg_value_in_loop"  // Name of the error variable
    private val delegateErrorVarName = "delegate_in_loop"
    private val refVarName = "msg_value_ref" // prefix of ref variables for variables referring to msg.value
    private val msgValueErrorVar = ErrorCmdGenerator.createErrorVar(monitorVarName)
    private val delegateErrorVar = ErrorCmdGenerator.createErrorVar(delegateErrorVarName)
    private val cfg = tacProgram.analysisCache.graph
    private val patching: SimplePatchingProgram = tacProgram.toPatchingProgram()
    private val cmdsInLoops = NodeLoopAssociator(tacProgram).computeCmdPtrs()
    private val delegateInLoop = DelegateCallInLoop(scene, tacProgram, cmdsInLoops, delegateErrorVar)

    /**
     * In case there is no reference to msg.value in the function the result is the original patching.
     * todo: avoid calling smt on such functions. Requires redesign of the builtin generator/checker.
     */
    data class NoMsgValueResult(val newProg: SimplePatchingProgram)

    data class MsgValueVarsDefsUses(
        val defs: Set<CmdPointer>,
        val uses: Set<CmdPointer>,
        val callValueVar: TACSymbol.Var?,
        val currentContractVar: TACSymbol.Var?
    )

    /**
     * @param[newVar] - new variable
     * The only patching not done at the end of the analysis adding newVar declaration is adding the declaration of
     * newVar.
     * Add newVar = false to the list of commands for patching after root at the end of the analysis.
     */
    private fun addFalseAfterRoot(
        newVar: TACSymbol.Var,
        cmdsAfterRoot: MutableList<SimpleCmdsWithDecls>
    ) {
        cmdsAfterRoot.add(
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(newVar, TACExprFactSimple.False)
            ).withDecls(newVar)
        )
    }

    /**
     * Add at the beginning of the program (after root succcessor):
     * assign msg_value_in_loop = false
     *  assume env.msg.value > 0 .
     *  Adds assume v > 0 for each v assigned env.msg.value.
     * The assignments to false to be added after root for ref vars are collected later at the creation of the ref vars.
     */
    private fun computeInitialInstrumentationOfRoots(callValueVar: TACSymbol.Var?):
        List<SimpleCmdsWithDecls> {
        // todo: we need envVar only if have to support env.msg.value that appear in the tac.
        // If callvaluevar is null, there is no msg.value in the function.
        val cmdsAfterRoot = mutableListOf<SimpleCmdsWithDecls>() // root -> command
        val roots = cfg.roots.map { it.ptr }
        check(roots.size == 1) { "Assumed one root" }
        addFalseAfterRoot(delegateErrorVar, cmdsAfterRoot = cmdsAfterRoot)
        addFalseAfterRoot(msgValueErrorVar, cmdsAfterRoot = cmdsAfterRoot)
        logger.debug { "callvalue def or use exists." }
        callValueVar?.let {
            val cond = TACExprFactSimple.Gt(
                it.asSym(), TACSymbol.Const(
                    BigInteger.ZERO,
                    Tag.Bit256
                ).asSym(),
                Tag.Bool
            )
            cmdsAfterRoot.add(listOf(TACCmd.Simple.AssumeExpCmd(cond, MetaMap())).withDecls())
        }
        return cmdsAfterRoot
    }


    /**
     * returns a list of assignment commands refVar = <expr representing msg.value ref in refExpr>
     * We need all the commands to patch in a specific CmdPointer because each node can be patched only once.
     * @param[node] - a node in the transitive closure of msg.value references and inside a loop.
     * @return the list of error instrumentation commands to be added after node.
     */
    private fun addErrorForMsgValueInLoopReference(
        node: CmdPointer, transitiveUseSites: Set<CmdPointer>, varToRefVar: Map<TACSymbol.Var, TACSymbol.Var>
    ): SimpleCmdsWithDecls? {
        check(node in cmdsInLoops && node in transitiveUseSites) {
            "A node inside loop and transitive use closure expected"
        }
        val lCommand = cfg.elab(node)
        val expr: TACExpr? = when (lCommand.cmd) {
            is TACCmd.Simple.AssigningCmd.AssignExpCmd -> {
                check(lCommand.cmd.lhs in varToRefVar) { "use site should have a refVar" }
                // errorVar = errorVar or refVar(lhs)
                varToRefVar[lCommand.cmd.lhs]!!.asSym()
            }

            is TACCmd.Simple.AssumeExpCmd -> {
                ErrorCmdGenerator.freeVarsRefExpr(lCommand.cmd.cond, varToRefVar)
            }

            is TACCmd.Simple.AssumeCmd -> {
                ErrorCmdGenerator.freeVarsRefExpr(lCommand.cmd.cond.asSym(), varToRefVar)
            }

            is TACCmd.Simple.AssumeNotCmd -> {
                ErrorCmdGenerator.freeVarsRefExpr(lCommand.cmd.cond.asSym(), varToRefVar)
            }

            is TACCmd.Simple.AssertCmd -> {
                ErrorCmdGenerator.freeVarsRefExpr(lCommand.cmd.o.asSym(), varToRefVar)
            }

            is TACCmd.Simple.ReturnCmd -> {  // o1 or o2
                val refExpr = ErrorCmdGenerator.freeVarsRefExpr(
                    TACExprFactSimple.LOr(
                        listOf(lCommand.cmd.o1.asSym(), lCommand.cmd.o2.asSym()), Tag.Bool
                    ),
                    varToRefVar
                )
                logger.debug { "${lCommand.cmd.o1} || ${lCommand.cmd.o2} return ref in loop" }
                refExpr
            }

            is TACCmd.Simple.ReturnSymCmd -> {
                ErrorCmdGenerator.freeVarsRefExpr(lCommand.cmd.o.asSym(), varToRefVar)
            }
            // todo: JumpiCmd is ignored here because of the assumption that there is an assignExpCmd with
            //  lhs = jump condition var for which the error assignment was added already. This assumption is wrong
            //  in case the assignment is outside the loop and the jump is inside.
            is TACCmd.Simple.JumpiCmd -> {
                val succ = cfg.succ(lCommand.ptr)
                val condition = cfg.pathConditionsOf(lCommand.ptr.block)[succ.first().block]?.getAsExpression()
                    ?: throw IllegalStateException(
                        "No path condition to reaching ${succ.first().block} " +
                            "from ${lCommand.ptr.block}"
                    )
                // Check that if the condition is a variable then it has a refvar. It doesn't check the condition is
                // assigned inside the loop.
                check(condition !is TACExpr.Sym.Var || condition.s in varToRefVar) {
                    "jumpi condition doesn't have a ref var $node"
                }
                null
            }

            is TACCmd.Simple.AssigningCmd.ByteLoad -> {
                byteLoadStoreExpr(loc = lCommand.cmd.loc, base = lCommand.cmd.base, varToRefVar = varToRefVar)
            }

            is TACCmd.Simple.AssigningCmd.ByteStore -> {
                byteLoadStoreExpr(
                    loc = lCommand.cmd.loc, base = lCommand.cmd.base, value = lCommand.cmd.value,
                    varToRefVar = varToRefVar
                )
            }

            is TACCmd.Simple.AssigningCmd.ByteStoreSingle -> {
                byteLoadStoreExpr(
                    loc = lCommand.cmd.loc, base = lCommand.cmd.base, value = lCommand.cmd.value,
                    varToRefVar = varToRefVar
                )
            }

            is TACCmd.Simple.AssigningCmd.WordLoad -> {
                byteLoadStoreExpr(
                    loc = lCommand.cmd.loc, base = lCommand.cmd.base,
                    varToRefVar = varToRefVar
                )
            }

            is TACCmd.Simple.WordStore -> {
                byteLoadStoreExpr(
                    loc = lCommand.cmd.loc, base = lCommand.cmd.base, value = lCommand.cmd.value,
                    varToRefVar = varToRefVar
                )
            }

            else -> {
                null
            }
        }
        return expr?.let { ErrorCmdGenerator.errorVarUpdateCmd(msgValueErrorVar, expr) }
    }

    private fun byteLoadStoreExpr(
        loc: TACSymbol, base: TACSymbol, value: TACSymbol? = null,
        varToRefVar: Map<TACSymbol.Var, TACSymbol.Var>
    )
        : TACExpr {
        val vars = byteLoadStoreArgList(loc, base, value)
        return TACExprFactSimple.LOr(vars.map { ErrorCmdGenerator.freeVarsRefExpr(it, varToRefVar) }, Tag.Bool)
    }

    /**
     * Add false assignments and assime msg.value > 0
     * We are adding after the successor of root because when adding after root it disappeared.
     */
    private fun addInstrumentationToRoot(cmdsAfterRoots: List<SimpleCmdsWithDecls>) {
        val roots = cfg.roots.map { it.ptr }
        check(roots.size == 1) { "Expected one root but got ${roots.size}" }
        val root = roots.first()
        check(cfg.succ(root).size == 1) { "root $root has ${cfg.succ(root).size} successors instead of one" }
        patching.insertAfter(cfg.succ(root).first(), cmdsAfterRoots.flatMap { it.cmds })
        patching.addVarDecls(cmdsAfterRoots.flatMapToSet { it.varDecls })
    }

    /**
     * Add AssertNot(errorVar) before each sink node.
     * Todo: check that there is no collision with a node which is patched elsewhere.
     */
    private fun addInstrumentationToSinks() {
        cfg.sinks.forEach { lastLtacCmd ->
            val cmd = cfg.elab(lastLtacCmd.ptr).cmd
            if (!(cmd is TACCmd.Simple.ReturnCmd || cmd is TACCmd.Simple.ReturnSymCmd || cmd is TACCmd.Simple.RevertCmd)
            ) {
                logger.debug { "Last command $cmd is not return " }
            }

            val noMsgValueErrorVar = TACSymbol.Var("no$monitorVarName", Tag.Bool)
            val noDelegateErrorVar = TACSymbol.Var("no$delegateErrorVarName", Tag.Bool)
            patching.addVarDecl(noMsgValueErrorVar)
            patching.addVarDecl(noDelegateErrorVar)
            patching.addBefore(
                lastLtacCmd.ptr, listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(noDelegateErrorVar, TACExpr.UnaryExp.LNot(delegateErrorVar.asSym())),
                    TACCmd.Simple.AssertCmd(noDelegateErrorVar,"Verify loops don't have delegate calls"),
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(noMsgValueErrorVar, TACExpr.UnaryExp.LNot(msgValueErrorVar.asSym())),
                    TACCmd.Simple.AssertCmd(noMsgValueErrorVar,"Verify loops don't access `msg.value`"),
                )
            )
        }
    }

    /**
     * Add new var indicating reference to msg.value
     * Add decl
     * Add assignment to false after root
     */
    private fun addNewRefVar(cmdPtr: CmdPointer, varToRefVar: MutableMap<TACSymbol.Var, TACSymbol.Var>): TACSymbol.Var {
        require(cfg.elab(cmdPtr).cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd){
            "Only AssignExpCmds are assigned a ref var"}
        val assignCmd = cfg.elab(cmdPtr).cmd as TACCmd.Simple.AssigningCmd.AssignExpCmd
        val newVar = TACSymbol.Var(assignCmd.lhs.namePrefix + "_" + refVarName, Tag.Bool)
        varToRefVar[assignCmd.lhs] = newVar
        return newVar
    }

    /**
     * @param[cmdPtr] - the assignment command for whose lhs a ref var is added.
     * Variables are added only for assign commands. For uses in other commands the ref vars of the free vars in the
     * commands are used.
     * If cmdPointer is a direct use, ref_var = true is added to the list, otherwise ref_var = LOR of refVar(v) where v
     * in rhs is added to the list.
     * @return a list containing the command for patching the ref variable.
     * Later if [cmdPtr] is in a loop, an additional command will be generated for the error. All commands for
     * the same cmdPtr should be added together.
     */
    private fun generateRefVarCmd(
        cmdPtr: CmdPointer, msgValueDirectUses: Set<CmdPointer>,
        varToRefVar: MutableMap<TACSymbol.Var, TACSymbol.Var>
    ): SimpleCmdsWithDecls? {
        logger.debug { "addRefVar for $cmdPtr" }
        val ltaccmd = cfg.elab(cmdPtr)
        return if (ltaccmd.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
            val newRefVar = addNewRefVar(ltaccmd.ptr, varToRefVar)
            // add error = true after use site
            if (cmdPtr in msgValueDirectUses) {
                logger.debug { "Add instrumentation $newRefVar for direct ${ltaccmd.cmd.lhs}" }
                listOf(TACCmd.Simple.AssigningCmd.AssignExpCmd(newRefVar, TACExprFactSimple.True)).withDecls(newRefVar)
            } else {
                logger.debug { "Add instrumentation $newRefVar for  ${ltaccmd.cmd.lhs}" }
                // newRefVar = or of rhs ref vars
                listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        newRefVar,
                        ErrorCmdGenerator.freeVarsRefExpr(ltaccmd.cmd.rhs, varToRefVar)
                    )
                ).withDecls(newRefVar)
            }
        } else {
            null
        }
    }

    // The symbol tacValue is msg.value
    private fun varIsEVMMsgValue(v: TACSymbol.Var): Boolean =
        v.asSym().equivSym(TACKeyword.CALLVALUE)

    // The symbol tacAddress == this (current contract).
    private fun varIsCurrentContract(v: TACSymbol.Var): Boolean =
        v.asSym().equivSym(TACKeyword.ADDRESS)

    /**
     * Find defs and direct uses of msg.value.
     */
    private fun findMsgValueVarsDefsAndDirectUses():  MsgValueVarsDefsUses{
        // Assignments whose rhs is msg.value or lhs is CALLVALUE
        var callValueVar: TACSymbol.Var? = null
        var currentContractVar: TACSymbol.Var? = null
        val msgValueDefs = cfg.commands.filter { ltacCmd ->
            ltacCmd.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd &&
                varIsEVMMsgValue(ltacCmd.cmd.lhs)
        }.map{it.ptr}.toSet()
        if (msgValueDefs.isNotEmpty()){
            callValueVar = cfg.elab(msgValueDefs.first()).narrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>().cmd.lhs
        }
        // Direct uses
        val msgValueDirectUses = cfg.commands.filter { ltacCmd ->
            val exprs = when (ltacCmd.cmd) {
                is TACCmd.Simple.AssigningCmd.AssignExpCmd -> {
                    listOf(ltacCmd.cmd.rhs)
                }
                is TACCmd.Simple.AssumeExpCmd -> {
                    listOf(ltacCmd.cmd.cond)
                }
                is TACCmd.Simple.AssigningCmd.ByteLoad -> {
                    byteLoadStoreArgList(loc = ltacCmd.cmd.loc, base = ltacCmd.cmd.base)
                }
                is TACCmd.Simple.AssigningCmd.ByteStore -> {
                    byteLoadStoreArgList(loc = ltacCmd.cmd.loc, base = ltacCmd.cmd.base)
                }
                is TACCmd.Simple.AssigningCmd.ByteStoreSingle -> {
                    byteLoadStoreArgList(loc = ltacCmd.cmd.loc, base = ltacCmd.cmd.base)
                }
                is TACCmd.Simple.AssigningCmd.WordLoad -> {
                    byteLoadStoreArgList(loc = ltacCmd.cmd.loc, base = ltacCmd.cmd.base)
                }
                is TACCmd.Simple.WordStore -> {
                    byteLoadStoreArgList(loc = ltacCmd.cmd.loc, base = ltacCmd.cmd.base)
                }
                else -> {
                    listOf()
                }
            }
            exprs.any { e ->
                TACExprFreeVarsCollector.getFreeVars(e).any { v ->
                    val isMsgValueVar = varIsEVMMsgValue(v)
                    if (isMsgValueVar){
                        callValueVar = v
                    }
                    if (varIsCurrentContract(v)){
                        currentContractVar = v
                    }
                    isMsgValueVar
                }
            }
        }.map{it.ptr}.toSet()
        return MsgValueVarsDefsUses(msgValueDefs, msgValueDirectUses, callValueVar, currentContractVar)
    }

    /**
     * @return list of expressions in the command.
     */
    private fun byteLoadStoreArgList(loc: TACSymbol, base: TACSymbol, value: TACSymbol? = null)
        : List<TACExpr>{
        val vars = mutableListOf<TACExpr>()
        if (loc is TACSymbol.Var){
            vars.add(loc.asSym())
        }
        check (base is TACSymbol.Var){"base $base is not TACSymbol.Var"}
        vars.add(base.asSym())
        if (value is TACSymbol.Var){
            vars.add(value.asSym())
        }
        return vars
    }

    /**
     * Compute the transitive closure of useSites(msg.value).
     */
    private fun computeUseTransitiveClosure(msgValueDirectUses: Set<CmdPointer>, msgValueDefs: Set<CmdPointer>):
        Set<CmdPointer> {
        val transitiveUsesWorkList = object : VisitingWorklistIteration<CmdPointer, CmdPointer, Set<CmdPointer>>() {
            override fun process(it: CmdPointer): StepResult<CmdPointer, CmdPointer, Set<CmdPointer>> {
                val useSites = mutableSetOf<CmdPointer>()  // Can't use nullable because + is not allowed on nullable
                val cmd = cfg.elab(it).cmd
                if (cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
                    useSites.addAll(cfg.cache.use.useSitesAfter(cmd.lhs, it))
                }
                return StepResult.Ok(useSites, listOf(it))
            }

            override fun reduce(results: List<CmdPointer>): Set<CmdPointer> {
                return results.toSet()
            }
        }
        return transitiveUsesWorkList.submit(msgValueDirectUses + msgValueDefs)
    }

    /**
     * The order of patching:
     * For direct use site outside loop:
     * refVar = true
     * For direct use site inside loop
     * refvar=true
     * errorVar = errorVar LOR (LOR refvars in command)
     * for nondirect use outside loop:
     * refVar = LOR of refvars in command
     * for use inside loop
     * errorVar = errorVar LOR (LOR refvars in command)
     */
    private fun computeInstrumentationOfCmdsInTransitiveClosure(
        transitiveUseSites: Set<CmdPointer>,
        msgValueDirectUses: Set<CmdPointer>,
        cmdsAfterRoot: MutableList<SimpleCmdsWithDecls>
    ): Map<CmdPointer, MutableList<SimpleCmdsWithDecls>> {
        val varToRefVar = mutableMapOf<TACSymbol.Var, TACSymbol.Var>() // ref to msg.value vars
        val cmdToInstrumentation = mutableMapOf<CmdPointer, MutableList<SimpleCmdsWithDecls>>()
        transitiveUseSites.forEach { cmdPointer ->
            check(cmdPointer !in cmdToInstrumentation) { " The same cmdPointer occurs twice in instrumentation" }
            val cmdList = mutableListOf<SimpleCmdsWithDecls>()
            generateRefVarCmd(cmdPointer, msgValueDirectUses, varToRefVar)?.let{cmdList.add(it)}
            if (cmdPointer in cmdsInLoops) {
                val errorCmd = addErrorForMsgValueInLoopReference(
                    cmdPointer, transitiveUseSites,
                    varToRefVar = varToRefVar
                )
                // Cannot add after jumpi, so need to add after its predecessors.
                // If pred instrumentation exists, need to append to it.
                errorCmd?.let{cmdList.add(it)}
            }
            if (cmdList.isNotEmpty()) {
                cmdToInstrumentation[cmdPointer] = cmdList
            }
        }
        varToRefVar.values.forEach { v ->
            addFalseAfterRoot(v, cmdsAfterRoot)
        }
        return cmdToInstrumentation
    }

    /**
     * Perform the patching. At this point for each node cmdToInstrumentation(node) should have all the commands
     * to be added after node.
     * We assume that the intersection of roots and cmdToInstrumentation.keys is empty and the
     * intersection of sinks and cmdToInstrumentation.keys is empty.
     */
    private fun addInstrumentationToTAC(cmdsAfterRoot: List<SimpleCmdsWithDecls>,
                                        cmdToInstrumentation: Map<CmdPointer, List<SimpleCmdsWithDecls>>){
        addInstrumentationToRoot(cmdsAfterRoot)
        cmdToInstrumentation.forEachEntry { (node, commands) ->
            check (cfg.elab(node).cmd !is TACCmd.Simple.JumpiCmd){
                "JumpiCmd not expected in patching"}
            patching.insertAfter(node, commands.flatMap { it.cmds })
            patching.addVarDecls(commands.flatMapToSet { it.varDecls })
        }
        addInstrumentationToSinks()
    }

    /**
     * Special variables are generated in order to track transitive uses of msg.value in order to get smt reachability
     * analysis and not rely only on static analysis.
     * For each use of callValueVar, if it is inside a loop, generate a new error variable and add
     * errorVar = false at each root
     * errorVar = true at the use site for direct uses errorVar = expr representing the ref of the rhs to msg.value.
     */
    fun instrumentMsgValueOccurences(methodName: String, payableFunctions: Set<BigInteger>,
                                     methodIsFromMainContract: Boolean): NoMsgValueResult {
        logger.debug{"instrumentMsgValueOccurences for $methodName"}
        // Find the CmdPointers of the uses and defs of msg.value.
        val (msgValueDefs, msgValueDirectUses, callValueVar, currentContractVar) = findMsgValueVarsDefsAndDirectUses()
        // The analysis is run only if msg.value appear in the tac
        val cmdsAfterRoot = mutableListOf<SimpleCmdsWithDecls>()
        cmdsAfterRoot.addAll(computeInitialInstrumentationOfRoots(callValueVar))
        // need the map in advance
        val  cmdToInstrumentation = mutableMapOf<CmdPointer, MutableList<SimpleCmdsWithDecls>>()
        if ( msgValueDirectUses.isNotEmpty() || msgValueDefs.isNotEmpty() ) {
            // Find all uses of the transitive closure of msg.value under assignments. That is
            // tacCallValue is in the transitive use sites and if x = y and y is in the transitive use sites, then also
            // y is in the transitive use sites.
            val transitiveUseSites = computeUseTransitiveClosure(msgValueDirectUses, msgValueDefs)
            // compute the list of commands to be patched after each command that uses msg.value.
            cmdToInstrumentation.putAll(
                computeInstrumentationOfCmdsInTransitiveClosure(
                    transitiveUseSites,
                    msgValueDirectUses,
                    cmdsAfterRoot
                )
            )
        }
        currentContractVar?.let { contract ->
            // Find delegate calls in loops.
            if (payableFunctions.isNotEmpty() && methodIsFromMainContract) {
                delegateInLoop.findUnresolvedDelegateCalls(cmdToInstrumentation, contractAddressSym = contract,
                    payableFunctions = payableFunctions)
            }
        }
        // Do the patching
        if (cmdsAfterRoot.isNotEmpty() || cmdToInstrumentation.isNotEmpty()) {
            addInstrumentationToTAC(cmdsAfterRoot, cmdToInstrumentation)
        }
        return NoMsgValueResult(patching)
    }
}
