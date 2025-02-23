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

package rules.genericrulecheckers

import allocator.SuppressRemapWarning
import analysis.CmdPointer
import analysis.icfg.Inliner
import bridge.NamedContractIdentifier
import config.Config
import log.*
import rules.genericrulecheckers.helpers.ReachabilityTrackingManager
import scene.IScene
import spec.CVLKeywords
import spec.toVar
import tac.CallId
import tac.Tag
import vc.data.*
import vc.data.taccmdutils.CallAttributes.getUnresolvedCalls
import java.math.BigInteger
import datastructures.stdcollections.*
import rules.genericrulecheckers.helpers.InstrumentationPlaceholderCommandsManager
import rules.genericrulecheckers.helpers.InstrumentationPlaceholderCommandsManager.Companion.createPlaceholders
import spec.CVLDefinitionSite
import spec.cvlast.CVLType
import spec.getAsCVLVariable
import tac.ITACSymbol
import vc.data.tacexprutil.TACExprFactSimple
import tac.MetaMap
import utils.mapToSet

private val logger = Logger(LoggerTypes.GENERIC_RULE)

/**
 * @param[viewFunctions] - view function sighash
 * @param[contractAddress] - main contract address
 * @param[scene] - the scene for getting the view function names
 * @param[contractName] - contract id for getting the view function names
 * @param[oldUnresolved] - unresolved call commands from the original program
 *
 * Instrument each unresolved call with additional call to view functions v1..vn after or before the unresolved call.
 * For each unresolved call we will add an assertion for each pair of view functions, or for all at once.
 * The assertion for a pair of functions will be:
 * (v_i_Unresolved == v_i_Start && v_j_Unresolved == v_j_Start)
 *  || (v_i_Unresolved == v_i_End && v_j_Unresolved == v_j_End)
 * When asserting for all at once, we just generalize the assertion for n view functions.
 */
class ViewReentrancyInstrumenting(
    private val viewFunctions: Set<BigInteger>,
    private val contractAddress: ITACSymbol,
    private val contractName: NamedContractIdentifier,
    private val scene: IScene,
    private val oldUnresolved: List<LCallSummary>,
    private val originalCode: CoreTACProgram,
) {

    private val originalGraph = originalCode.analysisCache.graph
    private val originalRoot = originalGraph.roots.first().ptr
    /**
     * One for initializing reachability tracking
     * One for input equality instrumentation.
     * 2 * numViewFunctions * unresolved.size for injecting all view functions and the assume not reverted for each
     * (view function, unresolved) pair.
     */
    private val numPlaceHoldersAfterRoot: UInt = 2u * viewFunctions.size.toUInt() * oldUnresolved.size.toUInt() + 2u

    /**
     * For each (unresolved call, view function) - injection of the view function + replaceCommand for the assert
     *   + one replace command for assumes
     */
    private val numPlaceHoldersForSinkInjectionAndAsserts: UInt =
        (oldUnresolved.size * (2 * viewFunctions.size + 1) + 1).toUInt()
    // 1 assume + assert per unresolved.
    private val numPlaceHoldersForAsserts: UInt = (oldUnresolved.size + 1).toUInt()
    /**
     * The output from injecting before/after unresolved call
     */
    data class NearUnresolvedInjectionOutput(
        val toReachVars: List<TACSymbol.Var>,
        val unresolvedCallIds: Map<BigInteger, List<CallId>>
    )

    data class ViewInjectionOutput(
        val startCallIds: Map<BigInteger, List<CallId>>,
        val toReachVars: List<TACSymbol.Var>,
        val unresolvedCallIds: Map<BigInteger, List<CallId>>,
        val endCallIds: List<Map<BigInteger, List<CallId>>>,
    )

    /**
     * Located (i.e. with a [CmdPointer]) [CallSummary], in the spirit of [LTACCmd].
     * Even though a CallSummary Has a Remapper, this is not remapable, and should only be valid for a single
     * [CoreTACProgram].
     */
    @SuppressRemapWarning
    data class LCallSummary(val ptr: CmdPointer, val summary: CallSummary)

    /**
     * Adding annotation commands as placeholders for commands to be injected later.
     * @return a program with annotation commands injected after the root, before/after each unresolved call,
     * before each sink.
     * At the root call, and each sink an AnnotationCmd for each view function injection and reachability.
     */
    private fun addPlaceHolders()
    : Pair<CoreTACProgram, InstrumentationPlaceholderCommandsManager> {
        val sinkPtrs = originalGraph.sinks.mapToSet { it.ptr }
        check(oldUnresolved.all {
            !(originalRoot == it.ptr || sinkPtrs.contains(it.ptr))
        }) { "Injecting view functions fails when a root or a sink of the program is an unresolved call." }
        val placeholdersLocs = mutableListOf<InstrumentationPlaceholderCommandsManager.PlaceholdersLocation>(
            // One for initializing reachability tracking
            // One for input equality instrumentation.
            // numViewFunctions * unresolved.size for injecting all view functions.
            InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.After(originalGraph.roots.first().ptr,
                numPlaceHoldersAfterRoot),
        )
        // For exhaustive case:
        // At each sink, for each unresolved, injection of each view function, assertion for each view function pair,
        // For non-exhaustive:
        // assertion on all view functions at the start, assertion on all view functions at sink.
        for (sink in originalGraph.sinks) {
            // numViewFunctions * unresolved.size for injection of view function
            // one replace command for assertions for each unresolved
            // injection of all view functions for each unresolved in order to get endCallId per (view, unresolved)
            placeholdersLocs.add(InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.Before(sink.ptr,
                numPlaceHoldersForSinkInjectionAndAsserts))
        }

        // Placeholders after unresolved calls
        for (lCall in oldUnresolved) {
            // One for reachability of unresolved
            // For each view function one for injection + one assume not reverted (therefore 2 * viewFunctions).
            if (Config.CheckViewReentrancyBeforeUnresolvedCall.get()) {
                placeholdersLocs.add(InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.Before(lCall.ptr,
                    (2 * viewFunctions.size + 1).toUInt()))
            } else {
                placeholdersLocs.add(InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.After(lCall.ptr,
                    (2 * viewFunctions.size + 1).toUInt()))
            }
        }

        return createPlaceholders(originalCode, placeholdersLocs)
    }

    /**
     * @param[extIndexVar] - variable for the index in the return buff of the call after unresolved that
     * should be equal to result at start or end
     * @param[callId] - CallId of the view function at the start/end
     * @param[extCallId] - CallId of the view function just after the unresolved call.
     * @return TACExpr for comparing one view result after unresolved call that did not revert to start/ end result.
     */
    private fun exprForCallResultEquality(extIndexVar: TACSymbol.Var, callId: CallId, extCallId: CallId)
        : TACExpr {
        val startOrEndSize = TACKeyword.RETURN_SIZE.toVar(callId)
        val extSize = TACKeyword.RETURN_SIZE.toVar(extCallId)
        return TACExpr.BinBoolOp.LAnd(
            listOf(
                // Equal to start/end (both out size and out buff) and start/end did not revert.
                callNotRevertedExp(),
                // Sizes equal
                TACExpr.BinRel.Eq(startOrEndSize.asSym(), extSize.asSym()),
                // For all indices buff is equal
                TACExpr.BinRel.Eq(
                    TACExpr.Select(
                        TACKeyword.RETURNDATA.toVar(callId).asSym(),
                        extIndexVar.asSym(),
                    ),
                    TACExpr.Select(
                        TACKeyword.RETURNDATA.toVar(extCallId).asSym(),
                        extIndexVar.asSym(),
                    ),
                )
            )
        )
    }


    /**
     * Create index vars for view vSigHash for all unresolved. The index vars are used to compare the contents of the
     * return buffer of the view function calls near the unresolved to the result at the start or end.
     * There are index variables for each unresolved, sinkIndex, view function tuple.
     * @param[sinkIndex] - the sink index for which the variables are generated.
     * @returns a map view function to a variable whose name contains sinkId, unresolved id, view function name.
     */
    private fun createIndexVars(
        sinkIndex: Int,
        prefix: String
    ): Map<BigInteger, TACSymbol.Var> {
        val indexVars = mutableMapOf<BigInteger, TACSymbol.Var>()
        for ( extInd in oldUnresolved.indices) {
            // index vars for one unresolved
            indexVars.putAll(viewFunctions.associateWith { vSigHash ->
                TACSymbol.Var(
                    "${prefix}Cmp__sink${sinkIndex}_call$extInd" +
                        scene.getMethod(contractName, vSigHash).name, Tag.Bit256)
            })
        }
        return indexVars
    }

    /**
     *  @returns List of AssumeCmds to be injected before the assertions before a sink and after the injections of
     *  the view functions.
     *  assume view did not revert at start, call. end.
     *  assume the index in the buffer is in bound
     *  assume the index is at word alignment.
     */
    private fun assumesBeforeSink(
        startCallIds: Map<BigInteger, List<CallId>>,
        endCallIds: Map<BigInteger, List<CallId>>,
        extCallIds: Map<BigInteger, List<CallId>>,
        startIndexVars: Map<BigInteger, TACSymbol.Var>,
        endIndexVars: Map<BigInteger, TACSymbol.Var>
    ): List<TACCmd.Simple> {
        val notReverted = (endCallIds.values + startCallIds.values + extCallIds.values).flatMap { callIds ->
            callIds.map { assumeCallNotReverted() }
        }
        // assume indexVar%32 == 0
        val wordAlignment = (startIndexVars.values + endIndexVars.values).map { assumeWordAlignment(it.asSym()) }
        // assume indexVar < start\endSize
        val inBounds = viewFunctions.flatMap { viewFunc ->
            // Safe to assume start\endCallIds contains all viewFunctions (checked at start of instrumentation)
            // Also safe to assume indexVars exist for each view function (checked at indexVar creation)
            startCallIds[viewFunc]!!.map {
                val size = TACKeyword.RETURN_SIZE.toVar(it).asSym()
                assumeIndexInBounds(startIndexVars[viewFunc]!!.asSym(), size)
            } + endCallIds[viewFunc]!!.map {
                val size = TACKeyword.RETURN_SIZE.toVar(it).asSym()
                assumeIndexInBounds(endIndexVars[viewFunc]!!.asSym(), size)
            }
        }
        return notReverted + inBounds + wordAlignment
    }

    /**
     * Injects an assertion before sink [sinkIndex] that checks that for each unresolved,
     * all view function results after/before the call
     * is equal to the result at start or the result of all view functions near the call is equal to the result at the
     * end.
     * @param[sinkIndex] - index of sink after which these assertions are injected.
     * @param[patching] - the current patching
     * @param[startIndexVars] - index variables for comparing to value at the start
     * @param[endIndexVars] - index variables for comparing to value at the end
     */
    private fun injectAssertOfAllViewFunctionsBeforeOneSink(
        injectionOutput: ViewInjectionOutput,
        phManager: InstrumentationPlaceholderCommandsManager,
        extCallIds: Map<BigInteger, List<CallId>>,
        sinkIndex: Int,
        originalSink: CmdPointer,
        patching: SimplePatchingProgram,
        startIndexVars: Map<BigInteger, TACSymbol.Var>,
        endIndexVars: Map<BigInteger, TACSymbol.Var>
    ): SimplePatchingProgram {

        /**
         * TACExpr for the condition that after unresolved call all view function results are are equal to start/end result.
         * @param[extIndexVars] - map view function -> variable for call to unresolved with index [extInd]
         * @return  command  assign v = for all view functions result after [extInd] unresolved == result at start/end
         * Might be used for contracts with many view functions for which all pair asserts are too much.
         */
        fun allEqualToUnresolvedExpr(
            extIndexVars: Map<BigInteger, TACSymbol.Var>,
            callIds: Map<BigInteger, List<CallId>>, extInd: Int,
        ): List<TACExpr> {
            // Unresolved call not reached or
            // all results after call == results after callIds[view] (which can be start or end callId).
            // Should be safe and full to iterate over viewFunctions
            return viewFunctions.map { vSigHash ->
                TACExprFactSimple.LOr(
                    TACExpr.UnaryExp.LNot(injectionOutput.toReachVars[extInd].asSym()),
                    exprForCallResultEquality(
                        extIndexVars[vSigHash]!!, callIds[vSigHash]!![extInd],
                        extCallIds[vSigHash]!![extInd]
                    ), Tag.Bool
                )
            }
        }

        for (extInd in oldUnresolved.indices) {
            val equalAtStart = allEqualToUnresolvedExpr(startIndexVars, injectionOutput.startCallIds, extInd)
            val startExpr = TACExprFactSimple.LAnd(equalAtStart, Tag.Bool)
            val equalAtEnd = allEqualToUnresolvedExpr(endIndexVars, injectionOutput.endCallIds[sinkIndex], extInd)
            // For all view functions result at call == result at end
            val endExpr = TACExprFactSimple.LAnd(equalAtEnd, Tag.Bool)

            val metaSrcInfo = originalGraph.elab(oldUnresolved[extInd].ptr).cmd.metaSrcInfo?.getSourceDetails()

            val assertVar = getAsCVLVariable(
                symbol = TACSymbol.Var("assertVar_sink${sinkIndex}_call${extInd}", Tag.Bool),
                cvlDefSite = CVLDefinitionSite.Rule(metaSrcInfo?.range),
                displayName = "behaveSameAtSink_${sinkIndex}_call$extInd",
                cvlType = CVLType.PureCVLType.Primitive.Bool
            )

            val cmdList =
                listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        assertVar,
                        TACExprFactSimple.LOr(
                            startExpr, endExpr, Tag.Bool
                        )
                    ),
                    SnippetCmd.CVLSnippetCmd.ViewReentrancyAssert(assertVar, functions = null, metaSrcInfo?.range).toAnnotation(),
                    TACCmd.Simple.AssertCmd(
                        assertVar,
                        "Possible Read-Only Reentrancy weakness at external call site at file " +
                            "${metaSrcInfo?.file ?: "Unknown File"}, line ${metaSrcInfo?.lineNumber ?: "Unknown Line"}"
                    ),
                    ScopeSnippet.toAnnotation()
                )
            patching.addVarDecls(setOf(assertVar))
            patching.replaceCommand(phManager.popFirst(originalSink)!!, cmdList)
        }
        return patching
    }

    private fun callNotRevertedExp() = TACExpr.UnaryExp.LNot(
        CVLKeywords.lastReverted.toVar().asSym()
    )

    private fun assumeCallNotReverted() = TACCmd.Simple.AssumeExpCmd(
        callNotRevertedExp()
    )

    private fun assumeWordAlignment(exp: TACExpr) = TACCmd.Simple.AssumeExpCmd(
        TACExpr.BinRel.Eq(
            TACExpr.BinOp.SMod(exp, TACSymbol.Const(BigInteger.valueOf(32), Tag.Bit256).asSym()),
            TACSymbol.Zero.asSym()
        )
    )

    private fun assumeIndexInBounds(exp1: TACExpr, exp2: TACExpr) = TACCmd.Simple.AssumeExpCmd(
        TACExpr.BinRel.Lt(exp1, exp2)
    )


    /**
     * Before each sink the following should be injected for each unresolved function:
     * 1. assume for every view function v endCallVar(v) == endCallResult(v).
     * 2. For every view function v and unresolved f assert result(v,f) == start || result(v,f) == end
     * 3. Do this for all pairs of v1 and v2 view functions
     * This is already supporting several unresolved in the same function.
     * Number of commands: 1 (assume) + <number of view functions> + 1 (for 2.)
     * @return patching with the following commands injected after sinkId for unresolved extInd:
     * for each view function pair add assign and assert for equality to result at start or at end.
     */
    private fun injectAssertionsByPairs(
        injectionOutput: ViewInjectionOutput,
        patching: SimplePatchingProgram,
        sinkIndex: Int,
        originalSink: CmdPointer,
        startIndexVars: Map<BigInteger, TACSymbol.Var>,
        endIndexVars: Map<BigInteger, TACSymbol.Var>,
        phManager: InstrumentationPlaceholderCommandsManager
    ): SimplePatchingProgram {
        for (extInd in oldUnresolved.indices) {  // i - index of unresolved function
            logger.debug { "replace placeholder for unresolved $extInd with assumes and assert" }
            // For each external call build assertion for each pair of view functions
            val cmdsAfterSink = mutableListOf<TACCmd.Simple>()
            val newAssertVars = mutableSetOf<TACSymbol.Var>()

            val visited = mutableSetOf<Pair<BigInteger, BigInteger>>()
            viewFunctions.forEach { vSigHash1 ->
                viewFunctions.forEach inner@{ vSigHash2 ->
                    if (vSigHash1 == vSigHash2 || Pair(vSigHash1, vSigHash2) in visited ||
                        Pair(vSigHash2, vSigHash1) in visited) {
                        return@inner
                    }
                    logger.debug { "Adding assert for $vSigHash1 and $vSigHash2" }
                    visited.add(Pair(vSigHash1, vSigHash2))
                    val vfName1 = scene.getMethod(contractName, vSigHash1).name
                    val vfName2 = scene.getMethod(contractName, vSigHash2).name
                    val (assertPairVar, cmds) = createAssertVarAndAssertCmds(sinkIndex, extInd, vfName1, vfName2)

                    newAssertVars.add(assertPairVar)
                    logger.debug { "oneSinkEndCallIds ${injectionOutput.endCallIds[sinkIndex]}" }

                    // Inner function for creating assertion logic commands.
                    fun getExprComparingViewFunctionsCallsToViewAtUnresolved(
                        extIndexVars: Map<BigInteger, TACSymbol.Var>,
                        callIds: Map<BigInteger, List<CallId>>,
                    ): TACExpr {
                        return TACExprFactSimple.LAnd(
                            // It is safe to access with index < unresolved.size and vSigHash in viewFunctions
                            listOf(
                                exprForCallResultEquality(
                                    extIndexVars[vSigHash1]!!,
                                    callIds[vSigHash1]!![extInd],
                                    injectionOutput.unresolvedCallIds[vSigHash1]!![extInd]
                                ),
                                exprForCallResultEquality(
                                    extIndexVars[vSigHash2]!!,
                                    callIds[vSigHash2]!![extInd],
                                    injectionOutput.unresolvedCallIds[vSigHash2]!![extInd]
                                )
                            ),
                            Tag.Bool
                        )
                    }

                    cmdsAfterSink.add(
                        // assert for a pair
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            assertPairVar,
                            TACExprFactSimple.LOr(
                                listOf(
                                    // Not reached
                                    TACExpr.UnaryExp.LNot(injectionOutput.toReachVars[extInd].asSym()),
                                    // case both view functions did not revert after unresolved.
                                    // Add the revert in the LOr when we support revert.
                                    getExprComparingViewFunctionsCallsToViewAtUnresolved(
                                        startIndexVars, injectionOutput.startCallIds),
                                    getExprComparingViewFunctionsCallsToViewAtUnresolved(
                                        endIndexVars, injectionOutput.endCallIds[sinkIndex],)
                                ), Tag.Bool
                            )
                        )
                    )
                    cmdsAfterSink.addAll(cmds)
                }
            }
            patching.run {
                addVarDecls(newAssertVars)
                replaceCommand(
                    phManager.popFirst(originalSink)!!,
                    cmdsAfterSink
                )
            }
        }
        return patching
    }

    /**
     * Creates a new variable and assert command for asserting view functions [vfName1], and [vfName2] are safe for
     * view reentrancy together. Does not put logic into the returned var.
     */
    private fun createAssertVarAndAssertCmds(
        sinkIndex: Int,
        extInd: Int,
        vfName1: String,
        vfName2: String
    ): Pair<TACSymbol.Var, List<TACCmd.Simple>> {
        val metaSrcInfo = originalGraph.elab(oldUnresolved[extInd].ptr).cmd.metaSrcInfo?.getSourceDetails()

        val assertPairVar = getAsCVLVariable(
            symbol = TACSymbol.Var("assertVar_${sinkIndex}_call${extInd}_${vfName1}_${vfName2}", Tag.Bool),
            cvlDefSite = CVLDefinitionSite.Rule(metaSrcInfo?.range),
            displayName = "behaveSame_${vfName1}_${vfName2}",
            cvlType = CVLType.PureCVLType.Primitive.Bool
        )
        val cmds = listOf(
            SnippetCmd.CVLSnippetCmd.ViewReentrancyAssert(assertPairVar, listOf(vfName1, vfName2), metaSrcInfo?.range)
                .toAnnotation(originalCode.destructiveOptimizations),
            TACCmd.Simple.AssertCmd(
                assertPairVar,
                "Possible Read-Only Reentrancy weakness at external call site at file " +
                "${metaSrcInfo?.file ?: "Unknown File"}, line ${metaSrcInfo?.lineNumber ?: "Unknown Line"} "+
                    "for functions " +  vfName1 + " and " + vfName2,
                meta = MetaMap(TACMeta.CVL_USER_DEFINED_ASSERT).plus(TACMeta.ISOLATED_ASSERT)
            ),
            ScopeSnippet.toAnnotation()
        )
        return Pair(assertPairVar, cmds)
    }

    private fun injectAllViewFunctionsAndGetCallIds(
        patching: SimplePatchingProgram,
        expanded: CoreTACProgram,
        phManager: InstrumentationPlaceholderCommandsManager
        ): ViewInjectionOutput {
        val startCallIds = injectAtStart(
            patching, expanded, phManager = phManager
        )
        val nearUnresolvedOutput = injectViewCallsAtUnresolvedCallIds(
            patching = patching,
            expanded = expanded,
            phManager = phManager,
            oldRoot = originalRoot
        )
        // TODO CERT-2703 : Figure out if I am on a reverting path and skip.
        // Get callIds of injections before sinks
        val viewToEndCallIds = injectBeforeSinks(
            patching,
            expanded,
            phManager
        )
        return ViewInjectionOutput(startCallIds, nearUnresolvedOutput.toReachVars,
            nearUnresolvedOutput.unresolvedCallIds, viewToEndCallIds)
    }

    /**
     * @return For each view function, map from call position to call id to be used later
     * For each view function, list of callIds at all startPtrs.
     */
    private fun injectAtStart(patching: SimplePatchingProgram,
                              expanded: CoreTACProgram,
                              phManager: InstrumentationPlaceholderCommandsManager,
    ): Map<BigInteger, List<CallId>> {
        val viewToCallIds = mutableMapOf<BigInteger, MutableList<CallId>>()
        oldUnresolved.indices.forEach { ind ->
            // Replace root nops by view function code
            viewFunctions.forEach { vsighash ->
                val vInstance = scene.getMethod(contractName, vsighash)
                val assumeNotRevertedPtr = phManager.popLast(originalRoot)!!
                val startCallId = Inliner.insertMethodCall(
                    expanded,
                    vInstance,
                    contractAddress as TACSymbol,
                    patching,
                    phManager.popLast(originalRoot)!!
                )
                viewToCallIds.computeIfAbsent(vsighash) { mutableListOf() }.add(startCallId)
                logger.debug {"start callid for view ${vInstance.name} unresolved $ind is $startCallId"}
                patching.replaceCommand(assumeNotRevertedPtr, listOf(assumeCallNotReverted()))
            }
        }
        return viewToCallIds
    }


    /**
     * 2 options for injecting assertions before the sinks.
     * 1. Only one view function or all function assert
     * 2. assertion for each pair of view function
     */
    private fun injectAssertions(
        patching: SimplePatchingProgram,
        phManager: InstrumentationPlaceholderCommandsManager,
        injectionOutput: ViewInjectionOutput
    ): SimplePatchingProgram {
        originalGraph.sinks.withIndex().forEach { (sinkIndex, sink) ->  // commands for one sink
            val oneSinkEndCallIds = injectionOutput.endCallIds[sinkIndex]
            val startIndexVars = createIndexVars(
                sinkIndex,
                "start"
            )
            val endIndexVars = createIndexVars(
                sinkIndex,
                "end"
            )
            check(startIndexVars.keys == viewFunctions) {"Expected index vars for all view functions but some " +
                "missing"}
            check(endIndexVars.keys == viewFunctions) {"Expected index vars for all view functions but some " +
                "missing"}
            check(injectionOutput.startCallIds.keys == viewFunctions) {"Each view function should appear in " +
                "functions injected at root."}
            check(oneSinkEndCallIds.keys == viewFunctions) {"Each view function should appear in " +
                "functions injected at sink."}
            viewFunctions.forEach { sighash ->
                // ptr per unresolved function
                check(oneSinkEndCallIds[sighash]!!.size == injectionOutput.startCallIds[sighash]!!.size) {
                    "${oneSinkEndCallIds[sighash]!!.size} callids at end " +
                        "but  ${injectionOutput.startCallIds.size} at start"
                }
                // Check size of phManager at sink
                check(phManager.sizeAt(sink.ptr) == numPlaceHoldersForAsserts) {
                    "Expected $numPlaceHoldersForAsserts placeholders for assert but got ${phManager.sizeAt(sink.ptr)}"}
            }
            val cmdList = assumesBeforeSink(
                startCallIds = injectionOutput.startCallIds, endCallIds = oneSinkEndCallIds,
                extCallIds = injectionOutput.unresolvedCallIds,
                startIndexVars, endIndexVars
            )
            patching.addVarDecls(startIndexVars.values.toSet())
            patching.addVarDecls(endIndexVars.values.toSet())
            patching.replaceCommand(phManager.popFirst(sink.ptr)!!, cmdList)
            // If we are not in exhaustive mode (i.e. all pairs), or we have only one view function run in single assert
            // mode
            if (injectionOutput.startCallIds.keys.size == 1 || !Config.ExhaustiveViewReentrancy.get()) {
                injectAssertOfAllViewFunctionsBeforeOneSink(
                    injectionOutput = injectionOutput,
                    extCallIds = injectionOutput.unresolvedCallIds,
                    sinkIndex = sinkIndex,
                    originalSink = sink.ptr,
                    patching = patching,
                    startIndexVars = startIndexVars,
                    endIndexVars = endIndexVars,
                    phManager = phManager)

            } else { // More than one view functions and per-pair assert
                injectAssertionsByPairs(
                    patching = patching,
                    injectionOutput = injectionOutput,
                    sinkIndex = sinkIndex,
                    startIndexVars = startIndexVars,
                    endIndexVars = endIndexVars,
                    originalSink = sink.ptr,
                    phManager = phManager
                )
            }
        }
        return patching
    }

    /**
     * For each start location, unresolved location, sink location
     * Add at the root:
     * The first AnnotationCmd at the root is replaced by the following list:
     * assume input buff size at start == input size at sink/unresolved
     * Initialize the input buffer at unresolved or sink to be equal to the input buffer at start.
     * inputbuffer(unresolved(view)) := inputBuffer(start (view) )
     * inputbuffer(sink (view)) := inputBuffer(start (view))
     * Number of annotation commands =|numViewFunctions| * |unresolved ptrs| for patching + 1 for initialization
     */
    private fun initInputVariablesValuesAtStart(patching: SimplePatchingProgram,
                                                where: CmdPointer,
                                                injectionOutput: ViewInjectionOutput,
                                             ) {
        // Check the number of callIds is the same for start, end and unresolved.
        // Accessing using viewFunctions should be safe.
        injectionOutput.endCallIds.forEach { oneSinkMap ->
            viewFunctions.forEach { vSigHash ->
                require(
                    vSigHash in oneSinkMap && vSigHash in injectionOutput.startCallIds
                        && vSigHash in injectionOutput.unresolvedCallIds &&
                    oneSinkMap[vSigHash]!!.size == injectionOutput.startCallIds[vSigHash]!!.size &&
                        oneSinkMap[vSigHash]!!.size == injectionOutput.unresolvedCallIds[vSigHash]!!.size
                )
                {
                    " ${oneSinkMap[vSigHash]?.size} at end but ${injectionOutput.startCallIds[vSigHash]?.size} " +
                        "at start ${injectionOutput.unresolvedCallIds[vSigHash]?.size} unresolved"
                }
            }
        }
        val toInject = mutableListOf<TACCmd.Simple>()
        injectionOutput.startCallIds.forEachEntry { (vsighash, unresolved) ->
            // For each startCallId there is a list of endCallIds per sink
            unresolved.indices.forEach { i ->
                // list for sinks
                val ends = injectionOutput.endCallIds.map { viewToUnresolved ->
                    check (vsighash in viewToUnresolved && vsighash in injectionOutput.startCallIds &&
                        viewToUnresolved[vsighash]!!.size == injectionOutput.startCallIds[vsighash]!!.size) {
                        "${injectionOutput.startCallIds.size} at start but " +
                        "${viewToUnresolved[vsighash]?.size} at end"}
                    viewToUnresolved[vsighash]!![i] }  // for each sink take the i'th unresolved in its list
                val start = injectionOutput.startCallIds[vsighash]!![i]  // The i'th call of vsighash
                val ext = injectionOutput.unresolvedCallIds[vsighash]!![i]
                // All ptrs of one unresolved
                toInject.addAll((ends + ext).flatMap {endOrExt ->
                    // assume inputLen at start == inputLen at ext
                    // assume inputlen at start == inputlen at end
                    listOf(
                        TACCmd.Simple.AssumeExpCmd(
                            TACExpr.BinRel.Eq(
                                Inliner.inputLenVar(start).asSym(),
                                Inliner.inputLenVar(endOrExt).asSym()
                            )
                        ),
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            Inliner.inputBuffVar(endOrExt),
                            Inliner.inputBuffVar(start)
                        ),
                    )
                })
            }
        }
        patching.replaceCommand(where, toInject)
    }

    /**
     * @param[expanded] - original code + injection of placeholders
     * Inject view function calls for each unresolved call * sink
     */
    private fun injectBeforeSinks(patching: SimplePatchingProgram,
                                  expanded: CoreTACProgram,
                                  phManager: InstrumentationPlaceholderCommandsManager): List<Map<BigInteger, List<CallId>>> {
        // Inject all view functions for each unresolved in order to get endCallId for each pair.
        val viewToEndCallIds = mutableListOf<MutableMap<BigInteger, MutableList<CallId>>>()
        // iterate on sinks
        originalGraph.sinks.forEachIndexed { sinkIdx, origSink ->
            viewToEndCallIds.add(mutableMapOf())
            // for injecting the views
            check(phManager.sizeAt(origSink.ptr) == numPlaceHoldersForSinkInjectionAndAsserts) {
                "Not enough placeholders for injection after sink"
            }

            // Should inject all view functions there
            viewFunctions.forEach { vsighash ->  // list of ptrs of one sink
                viewToEndCallIds.last().computeIfAbsent(vsighash) { mutableListOf() }
                val vInstance = scene.getMethod(contractName, vsighash)
                // inject vsighash numUnresolved times
                for (i in oldUnresolved.indices) {
                    // The last unresolved should be used to insert an assertion for each unresolved.
                    val callId = Inliner.insertMethodCall(
                        expanded,
                        vInstance,
                        contractAddress as TACSymbol,
                        patching,
                        phManager.popFirst(origSink.ptr)!!
                    )
                    // No revert of this injection
                    patching.replaceCommand(phManager.popFirst(origSink.ptr)!!, listOf(assumeCallNotReverted()))
                    logger.debug {"callid for sink $sinkIdx view ${vInstance.name} unresolved $i is $callId"}
                    // add callid to endIds of current view, sink
                    viewToEndCallIds.last()[vsighash]!!.add(callId)
                }
            }
        }
        return viewToEndCallIds
    }

    /**
     * Inject each view function before/after each unresolved. Add assumption that the call is not reverted.
     * jira: https://certora.atlassian.net/jira/software/c/projects/CERT/boards/29?assignee=612f302063f7bb006981d7a5
     * @param[expanded] - the program with place holders for injection.
     * todo CERT-2703 : support revert.
     */
    private fun injectViewCallsAtUnresolvedCallIds(
        patching: SimplePatchingProgram,
        expanded: CoreTACProgram,
        phManager: InstrumentationPlaceholderCommandsManager,
        oldRoot: CmdPointer,
    ): NearUnresolvedInjectionOutput {
        val reachUpdatePtrs = mutableListOf<CmdPointer>()
        // For each unresolved function, inject:
        // 1. reachability update to true
        // 2. calls to all view functions
        // 3. assume !lastrevert of the view injection
        // 4. Assumption unresolved call does not revert
        val unresolvedCallIds = mutableMapOf<BigInteger, MutableList<CallId>>()
        oldUnresolved.withIndex().forEach { (i, lCall) ->
            // Get the placeholders for the injection and reachability var update.
            // One pointer to update reachability tracking and one for injection.
            reachUpdatePtrs.add(phManager.popFirst(lCall.ptr)!!)

            // Cannot use the same loop of view functions for start/ unresolved/end because the injection pointers
            // change for each view function and it changes differently for each phase.
            viewFunctions.forEach { vsighash ->
                val vInstance = scene.getMethod(contractName, vsighash)
                val callId = Inliner.insertMethodCall(
                    expanded,
                    vInstance,
                    contractAddress as TACSymbol,
                    patching,
                    phManager.popFirst(lCall.ptr)!!
                )
                logger.debug {
                    "ext callid for view ${vInstance.name} unresolved $i is $callId"
                }
                unresolvedCallIds.computeIfAbsent(vsighash) { mutableListOf() }.add(callId)
                patching.replaceCommand(phManager.popFirst(lCall.ptr)!!, listOf(
                    assumeCallNotReverted(),
                ))
            }
        }
        // instrument update of tracking variables.
        val toReachVars = ReachabilityTrackingManager.addReachedTracking(
            patching, phManager.popLast(oldRoot)!!, reachUpdatePtrs, "ViewInjection"
        )

        // Always needs to be after, so phManager is not appropriate here.
        val newUnresolved = getUnresolvedCalls(expanded)
        check(newUnresolved.size == oldUnresolved.size)
        newUnresolved.forEach { lCall ->
            // Add assumption unresolved call succeeds right after the summary
            val summaryCallId = lCall.summary.callConvention.callerId
            val rc = TACKeyword.RETURNCODE.toVar(summaryCallId)
            val unresolvedSuccessCmd = TACCmd.Simple.AssumeExpCmd(
                TACExpr.UnaryExp.LNot(TACExpr.BinRel.Eq(0.asTACExpr, rc.asSym())))
            patching.insertAfter(lCall.ptr, listOf(unresolvedSuccessCmd))
            patching.addVarDecl(rc)

        }

        return NearUnresolvedInjectionOutput(toReachVars, unresolvedCallIds)
    }

    /**
     * Inject vInstance at the root, after each unresolved call and before each sink.
     * Add instrumentation for variables that track the reachability of the unresolved calls.
     * @param[expanded] - code with annotation placeholders for the instrumentation.
     * At the root in this order:
     * Initialization of inputBuffer variables.
     * Initialization of the reachVars.
     * One injection of the view functions for each unresolved function.
     */
    private fun injectViewCallsAndCommandsToMethod(
        expanded: CoreTACProgram,
        phManager: InstrumentationPlaceholderCommandsManager,
    ): CoreTACProgram {
        return with(expanded.toPatchingProgram()) {
            // recompute unresolved for expanded
            // Get new unresolved positions. Should have changed due to inserting nops
            val unresolved = getUnresolvedCalls(expanded).toList()
            if (unresolved.isNotEmpty()) {
                check(unresolved.size == oldUnresolved.size) {
                    "Number of new unresolved ${unresolved.size} but" +
                        "original number was ${oldUnresolved.size}"
                }
                // Inject view functions at the root and get startCallIds
                val injectionOutput = injectAllViewFunctionsAndGetCallIds(
                    patching = this, expanded = expanded, phManager = phManager)
                // Checks for amount of injected functions to later assume is correctly injected.
                checkInjection(injectionOutput.startCallIds)
                checkInjection(injectionOutput.unresolvedCallIds)
                injectionOutput.endCallIds.forEach { checkInjection(it) }

                check(injectionOutput.toReachVars.size == oldUnresolved.size) {"Each unresolved call site " +
                    "should have it's own reachability tracking var."}

                // Make sure we have input equality per call
                initInputVariablesValuesAtStart(
                    this, phManager.popFirst(originalRoot)!!, injectionOutput)
                // replace command for each unresolved
                // Each assert ptr if for (unresolved, view) and should check ((!ext_reach) || ext_revert ||
                //          (ext_out_size == start_out_size && ext_out == start_out && !start_revert)
                //          || (ext_out_size == end_out_size && ext_out == end_out && !end_revert)))
                // where ?_out_size, ?_out, ?_revert are the buffer size/ buffer /revert at view function call ?.
                // ext_reach - ext call was reached.
                injectAssertions(this, phManager, injectionOutput)
            }
            toCode(expanded)
        }
    }

    private fun checkInjection(callIdMap: Map<BigInteger, List<CallId>>) {
        check(callIdMap.keys == viewFunctions) {
            "Expecting all view functions to be injected at each instrumentation site."
        }
        check(callIdMap.values.all { it.size == oldUnresolved.size }) {
            "Expecting each view function to be injected once per unresolved call at root and sink injection sites."
        }
    }

    fun addInstrumentation(): CoreTACProgram {
       return if (viewFunctions.isNotEmpty()) {
            val (expanded, phManager) = addPlaceHolders()
            injectViewCallsAndCommandsToMethod(
                expanded = expanded,
                phManager = phManager,
            )
        } else {
           originalCode
        }
    }

}
