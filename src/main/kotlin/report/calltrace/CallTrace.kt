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

@file: Suppress("MoveVariableDeclarationIntoWhen")

package report.calltrace

import analysis.*
import analysis.icfg.Inliner
import analysis.icfg.Inliner.CallStack.STACK_POP
import analysis.icfg.Inliner.CallStack.STACK_PUSH
import analysis.icfg.SummaryStack
import analysis.ip.*
import config.Config
import config.ConfigType
import config.HardFailMode
import dwarf.InlinedFramesInfo
import sbf.tac.*
import evm.EVM_BITWIDTH256
import log.*
import report.CVTAlertReporter
import report.CVTAlertSeverity
import report.CVTAlertType
import report.DynamicSlicer
import report.RuleAlertReport
import report.calltrace.CallInputsAndOutputs.Dump
import report.calltrace.CallInstance.CVLExpInstance
import report.calltrace.CallInstance.InvokingInstance.CVLRootInstance
import report.calltrace.CallInstance.InvokingInstance.SolidityInvokeInstance
import report.calltrace.CallTrace.Companion.invoke
import report.calltrace.CallTrace.Failure
import report.calltrace.CallTrace.ViolationFound
import report.calltrace.formatter.CallTraceValueFormatter
import report.calltrace.formatter.CallTraceValue
import report.calltrace.printer.CallTracePrettyPrinter
import report.calltrace.sarif.*
import report.calltrace.sarif.FmtArg.CtfValue
import report.calltrace.sarif.SarifBuilder.Companion.mkSarif
import report.globalstate.GlobalState
import report.globalstate.toInstantiatedDisplayPath
import report.hasFailedInModel
import sbf.sbfLogger
import scene.IClonedContract
import scene.ISceneIdentifiers
import scene.MethodAttribute
import solver.CounterexampleModel
import spec.CVLReservedVariables
import spec.cvlast.*
import spec.cvlast.typedescriptors.EVMTypeDescriptor
import spec.cvlast.typedescriptors.VMTypeDescriptor
import tac.NBId
import tac.NBId.Companion.ROOT_CALL_ID
import utils.*
import vc.data.*
import vc.data.SnippetCmd.CVLSnippetCmd
import vc.data.TACMeta.CVL_LABEL_END
import vc.data.TACMeta.CVL_LABEL_START
import vc.data.TACMeta.CVL_LABEL_START_ID
import vc.data.TACMeta.SNIPPET
import vc.data.state.TACValue
import wasm.impCfg.*
import java.io.File
import java.util.*

/** Describes how the method call ended. */
enum class CallEndStatus(private val repString: String) {
    REVERT("REVERT"),
    THROW("THROW"),
    SUMMARIZED("SUMMARIZED"),
    DISPATCHER("DISPATCHER"),
    DEFAULT_HAVOC("DEFAULT HAVOC"),
    REVERT_CAUSE("REVERT CAUSE"),
    REVERT_DUMP("DUMP"),
    TRANSFER("TRANSFER"),
    VARIABLE_UNKNOWN("UNKNOWN"),
    VARIABLE_DONT_CARE("DONT CARE"),
    VARIABLE_CONCRETE("CONCRETE"),
    VARIABLE_HAVOC("HAVOC"),
    VARIABLE_HAVOC_DEPENDENT("HAVOC DEPENDENT"),
    ASSERT_CAST("ASSERT CAST"),
    NONE("")
    ;

    fun toJSONRepresentation(): String = repString
}

/** Attributes of the call trace */
enum class CallTraceAttribute(private val repString: String) {
    MESSAGE("message"),
    TEXT("text"),
    VALUE("value"),
    VALUES("values"),
    TOOLTIP("tooltip"),
    TYPE("type"),
    ARGUMENTS("arguments"),
    STATUS("status"),
    CHILDREN_LIST("childrenList"),
    JUMP_TO_DEFINITION("jumpToDefinition"),
    CHANGED_SINCE_PREV("changedSincePreviousPrint"),
    CHANGED_SINCE_START("changedSinceStart"),
    STORAGE_ID("storageId"),
    ;

    operator fun invoke(): String = repString
}

private val logger = Logger(LoggerTypes.CALLTRACE)
private val hardFail = Config.CallTraceHardFail.get() == HardFailMode.ON

/**
 * Attempts to generate a call trace for rule [ruleName], which is expected to be SAT.
 * Returns [CallTrace.ViolationFound] on success or [CallTrace.Failure] on any error.
 * The resulting class will contain a [callHierarchyRoot], which may only be
 * partially-built if an error occurred.
 */
private class CallTraceGenerator(
    val ruleName: String,
    val model: CounterexampleModel,
    val program: CoreTACProgram,
    val formatter: CallTraceValueFormatter,
    val scene: ISceneIdentifiers,
    ruleCallString: String,
) {
    val blocks = program.topoSortFw.filter { it in model.reachableNBIds }

    init {
        check(blocks.isNotEmpty()) {
            "set of reachable blocks is empty when trying to create call trace from model $model"
        }
    }

    val callInputsAndOutputs = CallInputsAndOutputs(formatter, blocks, model, program.analysisCache, scene)

    val callHierarchyRoot = initCallHierarchyRoot(ruleCallString)

    /**
     * sometimes the TAC structure is malformed, and we have structure like scope 1 start, scope 2 start, scope 1 end, scope 2 end.
     * in such cases when we see the end of scope 1 [currCallInstance] represent scope 2, and we may pop it from the call stack.
     * [earlyPoppedInstances] keeps the instances we popped without encounter their end snippet / annotation.
     */
    val earlyPoppedInstances: MutableList<CallInstance.ScopeInstance> = mutableListOf()

    var currCallInstance: CallInstance.ScopeInstance = callHierarchyRoot

    /**
     * [SnippetCmd.SolanaSnippetCmd.CexAttachLocation] can set the range for the next element in the calltrace that will
     * be processed to have reliable range information for Solana executables. This variable is set when
     * [SnippetCmd.SolanaSnippetCmd.CexAttachLocation] is found, and is consumed by the following calltrace entry that
     * needs range information.
     */
    var lastRangeSetByAttachLocationCmd: CVLRange.Range? = null

    val evaldCVLExpBuilder = EValdCVLExpAstBuilder(model, formatter)

    val graph = TACCommandGraph(program)

    val globalState = if (!Config.noCalltraceStorageInformation.get()) {
        GlobalState(blocks, graph, model, scene, formatter)
    } else {
        null
    }

    val sarifFormatter = SarifFormatter(formatter)

    /**
     * Adds a balance snippet [CallInstance] to the hierarchy of this [CallTrace].
     * [parent] is the parent of the newly created balance snippet [CallInstance].
     * [sym] is the [TACSymbol] which holds the loaded/stored value we want to represent in this generated [CallInstance].
     *
     * XXX: it looks like this is supposed to add a Transfer snippet call instance, is the function name wrong?
     */
    fun addBalanceSnippetCallInstance(
        parent: CallInstance.ScopeInstance,
        sym: TACSymbol,
        isLoad: Boolean,
        isSender: Boolean,
    ) {

        val prefix = when {
            isLoad && isSender -> "Load from: sender.balance"
            isLoad && !isSender -> "Load from: receiver.balance"
            !isLoad && isSender -> "Store at: sender.balance"
            else -> "Store at: receiver.balance"
        }

        Logger.regression { prefix }

        val valueArg = CtfValue.buildOrUnknown(
            tv = model.valueAsTACValue(sym),
            type = CVLType.PureCVLType.Primitive.UIntK(256),
            tooltip = "balance"
        )

        val sarif = sarifFormatter.fmt("{}{}{}", FmtArg(prefix), FmtArg.To, valueArg)

        parent.addChild(CallInstance.TransferInstance(sarif, CallEndStatus.NONE))
    }

    fun initCallHierarchyRoot(ruleCallString: String): CVLRootInstance {
        callInputsAndOutputs.initCVLCall(ROOT_CALL_ID)
        return CVLRootInstance(ruleCallString, formatter)
    }

    /**
     * This lets us overcome current architecture.
     * When a rule is compiled, assert and require commands are wrapped with start / end labels, which contain the cvl string.
     * commands inside CVL function are not wrapped, so for example "require a != 5" would appear as "a != 5".
     * When we process start label we create a CVLInvokeInstance with its label.
     * So in order to get similar result, we check here if the parent is CVLInvokeInstance, and if not we create it.
     */
    fun materializeCVLBoolCondExpInfoWithParent(cond: TACSymbol, namePrefix: String) {
        val label = evaldCVLExpBuilder.labelForSymbol(cond)
        val parentInstance = if (currCallInstance !is CallInstance.LabelInstance && label != null) {
            val rewrapped = CVLReportLabel.Message("$namePrefix $label", label.cvlRange)
            CallInstance.LabelInstance(rewrapped).also { callTraceAppend(it) }
        } else {
            currCallInstance
        }

        evaldCVLExpBuilder.materializeCVLBoolCondExpInfo(cond, parentInstance)
    }

    fun callTraceFailure(msg: () -> String): CallTrace {
        val errorMsg = "Failed to generate call trace for rule $ruleName: ${msg()}"
        val exception = CallTraceException(errorMsg)
        logger.error(errorMsg)
        return Failure(callHierarchyRoot, exception, printer)
    }

    fun invalidCallStack(msg: () -> String): CallTrace {
        return callTraceFailure { "invalid state of the call stack: ${msg()}\n${currCallInstance.printCallHierarchy()}\n" }
    }

    /**
     * checks the state of the call stack hierarchy satisfies [requirement].
     * sometimes, due to the way we put branch snippets, we have to pop them before the search (determined by [allowedToPop]).
     * note that it is a logic error for both [allowedToPop] and [requirement] to return true for the same [CallInstance.ScopeInstance].
     */
    fun ensureStackState(
        requirement: (CallInstance.ScopeInstance) -> Boolean,
        eventDescription: String,
        allowedToPop: (CallInstance.ScopeInstance) -> Boolean = { false },
        allowedToFail: Boolean = false,
        callback: (CallInstance.ScopeInstance) -> Unit = {}
    ): CallTrace? {
        while (allowedToPop(currCallInstance)) {
            earlyPoppedInstances.add(currCallInstance)
            callTracePop() ?: return invalidCallStack { "Failed to pop for $eventDescription" }
        }

        // the instance at the top of stack satisfies the requirement, so all good.
        if (requirement(currCallInstance)) {
            val matchingInstance = currCallInstance
            callTracePop()
                ?: return invalidCallStack { "Try to access parent of $currCallInstance when looking for $eventDescription." }
            callback(matchingInstance) // callback is intentionally after changing currCallInstance, so it can modify it if needed (like in revert path)
            return null
        }

        return if (allowedToFail) {
            warnOnWrongStackState(eventDescription)
            null
        } else {
            tryRecover(requirement, eventDescription, callback)
        }
    }

    fun tryRecover(
        requirement: (CallInstance.ScopeInstance) -> Boolean,
        eventDescription: String,
        callback: (CallInstance.ScopeInstance) -> Unit,
    ): CallTrace? {
        if (hardFail) {
            return invalidCallStack { "$eventDescription is not at top of call stack and hardFail is on." }
        }

        // look for first ancestor satisfying requirement.
        var curr: CallInstance.ScopeInstance? = currCallInstance
        val poppedInstances: MutableList<CallInstance.ScopeInstance> = mutableListOf()

        while (curr != null && !requirement(curr)) {
            poppedInstances.add(curr)
            curr = curr.parent
        }

        /**
         * we found a matching instance, but not at the top of the stack.
         * we are not in [hardFail] mode, so pop all instances and add them to [earlyPoppedInstances].
         */
        if (curr != null) {
            logger.warn { "Recovered from invalid call stack state in rule $ruleName for $eventDescription. stack:\n${currCallInstance.printCallHierarchy()}" }
            currCallInstance = curr.parent
                ?: return invalidCallStack { "Try to access parent of $currCallInstance when recovering the stack for $eventDescription." }
            earlyPoppedInstances.addAll(poppedInstances)
            callback(curr)
            return null
        }

        /**
         * the matching instance is not at the call stack.
         * check if we already popped it out prematurely.
         */
        val index = earlyPoppedInstances.indexOfFirst(requirement)

        // instance was not popped out of the call stack in the past.
        if (index == -1) {
            return invalidCallStack { "Missing $eventDescription." }
        }

        callback(earlyPoppedInstances[index])
        earlyPoppedInstances.removeAt(index)

        return null
    }

    fun warnOnWrongStackState(eventDescription: String) {
        val instance = CallInstance.ErrorInstance.WrongStackState()
        callTracePush(instance)

        CVTAlertReporter.reportAlert(
            type = CVTAlertType.DIAGNOSABILITY,
            severity = CVTAlertSeverity.WARNING,
            jumpToDefinition = null,
            message = "Call trace reached unexpected state in rule: ${this.ruleName}",
            hint = "Check the rule's call stack to see where this happened",
            url = null,
        )

        logger.warn { "Execution of call trace in rule ${this.ruleName} recovered - expected $eventDescription" }
    }

    /**
     * Stopgap solution for error handling. Generally, we don't expect [generate] to throw.
     * But in case it does, we wrap the exception in a [CallTrace.Failure] along with the
     * [callHierarchyRoot] built up to that point. This means we'll still return a [CallTrace].
     */
    fun safeGenerate(): CallTrace {
        return if (program.destructiveOptimizations) {
            @OptIn(Config.DestructiveOptimizationsOption::class)
            CallTrace.DisabledByConfig(callHierarchyRoot, Config.DestructiveOptimizationsMode)
        } else {
            @Suppress("TooGenericExceptionCaught")
            try {
                generate()
            } catch (e: Exception) {
                val generationFailureMsg =
                    "CallTrace generation ended prematurely due to unexpected exception (rule $ruleName)"
                logger.error(e) { generationFailureMsg }
                val exception = CallTraceException(generationFailureMsg, e)
                Failure(callHierarchyRoot, exception, printer)
            } finally {
                printer?.close()
            }
        }
    }

    fun handleAssigningCmd(cmd: TACCmd.Simple.AssigningCmd): CallTrace? {
        globalState?.handleAssignments(cmd)

        if (cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
            return null
        }

        val assignment: TACCmd.Simple.AssigningCmd.AssignExpCmd = cmd
        evaldCVLExpBuilder.step(assignment)

        val movementCallIndex = currCallInstance.ancestorOfType<SolidityInvokeInstance>()?.callIndex
        if (movementCallIndex != null && callInputsAndOutputs.externalCall(movementCallIndex) != null) {
            val calldataMovements = assignment.calldataMovement(model, movementCallIndex)
            calldataMovements.forEach { calldataMovement ->
                printer?.callDataMovement(calldataMovement)
                callInputsAndOutputs.registerCalldataMovement(calldataMovement, movementCallIndex)
            }

            val returndataMovement = assignment.returndataMovement(model)
            printer?.returnDataMovement(returndataMovement)
            callInputsAndOutputs.registerReturndataMovement(returndataMovement, movementCallIndex)
        }

        return null
    }

    fun handleAssumeCmd(cmd: TACCmd.Simple.AssumeCmd): CallTrace? {
        if (cmd.cond is TACSymbol.Var && cmd.cond.meta.contains(TACMeta.CVL_IF_PREDICATE)) {
            // suppress outputting a call instance for the predicate of
            // the `if` command we just evaluated, since we already got it
            // from the snippet at the beginning of the `if`
        } else {
            materializeCVLBoolCondExpInfoWithParent(cmd.cond, "require")
        }

        return null
    }

    fun handleAssert(cmd: TACCmd.Simple.AssertCmd, currBlock: NBId, idx: Int): CallTrace? {
        materializeCVLBoolCondExpInfoWithParent(cmd.o, "assert")

        Logger.regression { "Got assert command with message: ${cmd.msg}" }

        val hasFailed = cmd.hasFailedInModel(model, CmdPointer(currBlock, idx)).getOrThrow()
        if (hasFailed) {
            globalState?.computeGlobalState(formatter = formatter)?.let(::callTraceAppend)

            val violatedAssert = LTACCmd(CmdPointer(currBlock, idx), cmd as TACCmd.Simple)
            return ViolationFound(callHierarchyRoot, violatedAssert)
        }

        return null
    }

    fun handleCvlLabelStart(value: CVLReportLabel, labelId: Int): CallTrace? {
        val instance = CallInstance.LabelInstance(value, labelId)
        callTracePush(instance)
        return null
    }

    fun handleCvlLabelEnd(id: Int): CallTrace? {
        return ensureStackState(
            requirement = { (it as? CVLSnippetCmd.EventID)?.id == id },
            eventDescription = "event with ID $id",
            callback = { }
        )
    }

    fun handleInternalFuncStart(internalFuncStartAnnot: InternalFuncStartAnnotation): CallTrace? {
        val funcName = internalFuncStartAnnot.methodSignature.qualifiedMethodName.toString()

        val caller = currCallInstance.ancestorOfType<SolidityInvokeInstance>()
        val callIndexOfCaller = when (caller) {
            is SolidityInvokeInstance.External -> caller.callIndex
            is SolidityInvokeInstance.Internal -> caller.callIndexOfCaller
            else -> {
                return invalidCallStack { "Missing a caller for the internal function $funcName (id = ${internalFuncStartAnnot.id})" }
            }
        }

        val instance = SolidityInvokeInstance.Internal(
            funcName,
            internalFuncStartAnnot.id,
            callIndexOfCaller,
            internalFuncStartAnnot,
            formatter,
        )

        val paramValues = internalFuncStartAnnot.args
            .filter { it.sort == InternalArgSort.SCALAR || it.sort == InternalArgSort.CALLDATA_ARRAY_ELEMS }
            .associateNotNull { arg ->
                val pos = internalFuncStartAnnot.stackOffsetToArgPos[arg.offset] ?: return@associateNotNull null
                val tacValue = model.valueAsTACValue(arg.s) ?: return@associateNotNull null

                pos to tacValue
            }

        val dump = Dump.Parameters(instance.paramTypes, instance.paramNames)
        callInputsAndOutputs.writeDumpToCall(dump, paramValues, instance)

        Logger.regression {
            "CallTrace: internal call: (internal) ${internalFuncStartAnnot.methodSignature.prettyPrint()}"
        }
        callTracePush(instance)

        return null
    }

    val printer =
        if (Config.CallTraceTextDump.get()) {
            CallTracePrettyPrinter(ruleName, model)
        } else {
            null
        }

    /** Push one level to the call stack. */
    private fun callTracePush(instance: CallInstance.ScopeInstance) {
        callTraceAppend(instance)
        currCallInstance = instance
        printer?.push(instance)
    }

    /** Append a node (representing a command or similar) to the current level of the call stack. */
    private fun callTraceAppend(instance: CallInstance) {
        currCallInstance.addChild(instance)
        printer?.append(instance)
    }

    /** Pop one level of the call stack; returns null when we're already at top level (i.e. [currCallInstance] has no
     * parent) */
    private fun callTracePop(): CallInstance.ScopeInstance? {
        val parent = currCallInstance.parent
        if (parent != null) {
            currCallInstance = parent
            printer?.pop()
        }
        return parent
    }


    fun handleInternalFuncExit(internalFuncExitAnnot: InternalFuncExitAnnotation): CallTrace? {
        val funcName = internalFuncExitAnnot.methodSignature.qualifiedMethodName.toString()

        return ensureStackState(
            requirement = { it is SolidityInvokeInstance.Internal && it.id == internalFuncExitAnnot.id },
            eventDescription = "start of internal function $funcName (id = ${internalFuncExitAnnot.id})",
            allowedToPop = { it is CallInstance.BranchInstance.Start },
            allowedToFail = true,
            callback = {
                val internalInvokingInstance = it as SolidityInvokeInstance.Internal

                val internalReturnValues = internalFuncExitAnnot.rets.retValsInModel(model)

                val dump = Dump.ReturnValues(internalInvokingInstance.returnTypes)
                callInputsAndOutputs.writeDumpToCall(dump, internalReturnValues, internalInvokingInstance)

                globalState?.computeGlobalState(formatter = formatter)?.let(::callTraceAppend)

                Logger.regression {
                    "$internalInvokingInstance / ${internalInvokingInstance.returnValuesToString()}"
                }
            }
        )
    }

    fun handleStackPush(pushRecord: Inliner.CallStack.PushRecord): CallTrace? {
        val newInstance = SolidityInvokeInstance.External(
            formatCallee(pushRecord.callee, scene) ?: "unknown callee",
            pushRecord.calleeId,
            pushRecord.callee.attr == MethodAttribute.Unique.Constructor,
            pushRecord.callee.resolveIn(scene)?.evmExternalMethodInfo,
            formatter,
        )


        val caller = (currCallInstance as? CallInstance.InvokingInstance<*>)
        // an imho more correct version, but not worth it just for the regtests:
        // currCallInstance.ancestorOfType<CallInstance.InvokingInstance<*>>()
        Logger.regression {
            "CallTrace: caller: " + (caller?.toStringWithoutParamValues()
                ?: currCallInstance.name) + " callee: " + newInstance.toStringWithoutParamValues()
        }
        callTracePush(newInstance)
        return null
    }

    fun handleStackPop(popRecord: Inliner.CallStack.PopRecord): CallTrace? {
        val calleeName = formatCallee(popRecord.callee, scene) ?: "unknown callee"

        return ensureStackState(
            requirement = { it is SolidityInvokeInstance.External && it.callIndex == popRecord.calleeId },
            eventDescription = "start of external function $calleeName (id = ${popRecord.calleeId})",
            allowedToPop = { it is CallInstance.BranchInstance.Start },
            callback = {
                val call = it as SolidityInvokeInstance.External
                callInputsAndOutputs.finalizeExternalCall(call)

                Logger.regression {
                    "$call / ${call.returnValuesToString()}"
                }
            }
        )
    }

    fun handleRevertPath(cmd: TACCmd.Simple, currBlock: NBId, idx: Int): CallTrace? {
        currCallInstance.status = CallEndStatus.REVERT

        val revertSliceResults = try {
            DynamicSlicer(program, model, scene).sliceRevertCond(LTACCmd(CmdPointer(currBlock, idx), cmd).narrow())
        } catch (e: Exception) {
            logger.warn(e) {
                "Failed to slice the revert condition @ ${
                    CmdPointer(
                        currBlock,
                        idx
                    )
                } while constructing the call trace on the rule $ruleName"
            }
            null
        }
        if (revertSliceResults != null) {
            val revertCauseInstance = CallInstance.InvokingInstance.RevertCauseHeaderInstance().also {
                callTraceAppend(it)
            }
            val srcDetailsInstanceOrNull = revertSliceResults.sourceDetails?.let {
                val srcDetailsInstance = CallInstance.InvokingInstance.RevertCauseSrcDetailsInstance(it)
                revertCauseInstance.addChild(srcDetailsInstance)
                srcDetailsInstance
            }
            revertSliceResults.sliceExprPrintRep.let {
                val inst = srcDetailsInstanceOrNull ?: revertCauseInstance
                inst.addChild(CallInstance.InvokingInstance.RevertCauseDumpInstance(it))
            }
        }

        return ensureStackState(
            requirement = { it !is SolidityInvokeInstance.Internal },
            eventDescription = "Solidity function call",
            allowedToPop = { it is CallInstance.BranchInstance || it is SolidityInvokeInstance.Internal },
            callback = {
                it.status = CallEndStatus.REVERT
                currCallInstance = it
            }
        )
    }

    fun handleThrowPath(): CallTrace? {
        currCallInstance.status = CallEndStatus.THROW
        return null
    }

    fun handleSummaryStart(summStart: SummaryStack.SummaryStart, currBlock: NBId, idx: Int): CallTrace? {
        val summaryInstance = CallInstance.InvokingInstance.SummaryInstance(currBlock, idx, summStart, scene, formatter)

        callTracePush(summaryInstance)
        return null
    }

    fun handleExternalSummaryEnd(externalSummaryEnd: SummaryStack.SummaryEnd.External): CallTrace? {
        return ensureStackState(
            requirement = { it is CallInstance.InvokingInstance.SummaryInstance },
            eventDescription = "END_EXTERNAL_SUMMARY for ${externalSummaryEnd.appliedSummary}"
        )
    }

    fun handleInternalSummaryEnd(internalFuncExitAnnot: SummaryStack.SummaryEnd.Internal): CallTrace? {
        return ensureStackState(
            requirement = { it is CallInstance.InvokingInstance.SummaryInstance },
            eventDescription = "END_INTERNAL_SUMMARY for function ${internalFuncExitAnnot.methodSignature.prettyPrint()}",
            callback = {
                val invokingInstance = it as CallInstance.InvokingInstance.VMInvokingInstance
                val returnValues = internalFuncExitAnnot.rets.retValsInModel(model)
                val dump = Dump.ReturnValues(invokingInstance.returnTypes)
                callInputsAndOutputs.writeDumpToCall(dump, returnValues, invokingInstance)
            }
        )
    }

    private fun SnippetCmd.EVMSnippetCmd.EVMStorageAccess.accessLocation(): Sarif = when (this) {
        is SnippetCmd.EVMSnippetCmd.RawStorageAccess.WithLocSym -> {
            val storageAddress =
                CtfValue.buildOrUnknown(
                    tv = model.valueAsTACValue(loc),
                    type = EVMTypeDescriptor.address,
                    tooltip = "address"
                )
            sarifFormatter.fmt("[raw storage address] {}", storageAddress)
        }

        is SnippetCmd.EVMSnippetCmd.RawStorageAccess.WithPath ->
            sarifFormatter.fmt("[raw storage path] {}", FmtArg(path.toString()))

        is SnippetCmd.EVMSnippetCmd.StorageSnippet -> {
            val dp = this.displayPath.toDisplayString(formatter, model) // should eventually be a sarif
            sarifFormatter.fmt("{}", FmtArg(dp))
        }

    }

    private fun SnippetCmd.EVMSnippetCmd.EVMStorageAccess.referredStorageMessage(): Sarif = mkSarif {
        val accessLocation = accessLocation()
        val tv = value?.let(model::valueAsTACValue)

        append(scene.getContract(contractInstance).name)
        append(".")
        append(accessLocation)

        if (tv != null) {
            val type = storageType ?: EVMTypeDescriptor.UIntK(EVM_BITWIDTH256)
            val addressArg = CallTraceValue.evmCtfValueOrUnknown(
                    scalarValue = tv,
                    type = type,
                ).toSarif(formatter, tooltip = "storage value")

            append(Sarif.EVALUATES_TO)
            append(addressArg)
        }

        printer?.snippet(this@referredStorageMessage as SnippetCmd)
    }

    fun handleStorageSnippet(snippetCmd: SnippetCmd.EVMSnippetCmd.StorageSnippet): CallTrace? {
        val referredStorageMsg = snippetCmd.referredStorageMessage()

        // only used for regression logging
        val pathAsString = snippetCmd.displayPath.toNonIndexedString()

        globalState?.handleStorageLocalChanges(snippetCmd)
        printer?.localStorageChange(snippetCmd)

        val range = snippetCmd.range
        val snippetCallInstance = when (snippetCmd) {
            is SnippetCmd.EVMSnippetCmd.StorageSnippet.StoreSnippet -> {
                Logger.regression {
                    "Store at: $pathAsString"
                }
                CallInstance.StorageInstance.Store(
                    sarifFormatter.fmt("Store at {}", FmtArg(referredStorageMsg)),
                    range,
                )
            }

            is SnippetCmd.EVMSnippetCmd.StorageSnippet.DirectStorageLoad,
            is SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet -> {
                Logger.regression {
                    "Load from: $pathAsString"
                }
                CallInstance.StorageInstance.Load(
                    sarifFormatter.fmt("Load from {}", FmtArg(referredStorageMsg)),
                    range,
                )
            }

            is SnippetCmd.EVMSnippetCmd.StorageSnippet.DirectStorageHavoc -> {
                Logger.regression {
                    "Havoc of: $pathAsString"
                }
                /** do we really want to show the actual value here even though it was just havoced? */
                CallInstance.StorageInstance.Havoc(
                    sarifFormatter.fmt("Havoc of {}", FmtArg(referredStorageMsg)),
                    range,
                )
            }
        }
        callTraceAppend(snippetCallInstance)
        return null
    }

    private fun handleRawStorageSnippet(snippetCmd: SnippetCmd.EVMSnippetCmd.RawStorageAccess) {
        val isLoad = snippetCmd.isLoad
        val referredStorageMsg = snippetCmd.referredStorageMessage()
        val range = snippetCmd.range
        val builder = SarifBuilder()
        val callInstance =
            if (isLoad) {
                builder.append("Load from ")
                builder.append(referredStorageMsg)
                CallInstance.StorageInstance.Load(builder.build(), range)
            } else {
                builder.append("Store at ")
                builder.append(referredStorageMsg)
                CallInstance.StorageInstance.Store(builder.build(), range)
            }
        callTraceAppend(callInstance)
    }

    fun handleBalanceSnippet(snippetCmd: SnippetCmd.EVMSnippetCmd.ReadBalanceSnippet): CallTrace? {
        globalState?.handleBalanceSnippet(snippetCmd)
        val addr = CtfValue.buildOrUnknown(
            tv = model.valueAsTACValue(snippetCmd.addr),
            type = EVMTypeDescriptor.address,
            tooltip = "address"
        )
        val balance =
            CtfValue.buildOrUnknown(
                tv = model.valueAsTACValue(snippetCmd.balance),
                type = EVMTypeDescriptor.UIntK(256),
                tooltip = "balance",
            )
        val sarif = sarifFormatter.fmt("{}.balance{}{}", addr, FmtArg.To, balance)

        val balanceInstance = CallInstance.BalanceInstance(sarif)
        callTraceAppend(balanceInstance)
        return null
    }

    fun handleTransferSnippet(snippetCmd: SnippetCmd.EVMSnippetCmd.TransferSnippet): CallTrace? {
        globalState?.handleTransferSnippet(snippetCmd)
        val sender = CtfValue.buildOrUnknown(
            tv = model.valueAsTACValue(snippetCmd.srcAccountInfo.addr),
            type = EVMTypeDescriptor.address,
            tooltip = "address of sender"
        )
        val receiver = CtfValue.buildOrUnknown(
            tv = model.valueAsTACValue(snippetCmd.trgAccountInfo.addr),
            type = EVMTypeDescriptor.address,
            tooltip = "address of receiver"
        )
        val transferred = CtfValue.buildOrUnknown(
            tv = model.valueAsTACValue(snippetCmd.transferredAmount),
            type = EVMTypeDescriptor.UIntK(256),
            tooltip = "transferred amount"
        )
        val sarif =
            sarifFormatter.fmt("sender: {}; receiver: {}; transferred amount: {}", sender, receiver, transferred)

        val snippetCallInstance = CallInstance.TransferInstance(sarif, CallEndStatus.TRANSFER)

        callTraceAppend(snippetCallInstance)

        addBalanceSnippetCallInstance(
            parent = snippetCallInstance,
            sym = snippetCmd.srcAccountInfo.old,
            isLoad = true,
            isSender = true
        )
        addBalanceSnippetCallInstance(
            parent = snippetCallInstance,
            sym = snippetCmd.srcAccountInfo.new,
            isLoad = false,
            isSender = true
        )
        addBalanceSnippetCallInstance(
            parent = snippetCallInstance,
            sym = snippetCmd.trgAccountInfo.old,
            isLoad = true,
            isSender = false
        )
        addBalanceSnippetCallInstance(
            parent = snippetCallInstance,
            sym = snippetCmd.trgAccountInfo.new,
            isLoad = false,
            isSender = false
        )

        return null
    }

    fun handleStartLoopSnippet(snippetCmd: SnippetCmd.EVMSnippetCmd.LoopSnippet.StartLoopSnippet): CallTrace? {
        val snippetCallInstance = CallInstance.LoopInstance.Start(
            snippetCmd.loopSource,
            snippetCmd.loopIndex
        )
        Logger.regression {
            snippetCmd.loopSource
        }
        callTracePush(snippetCallInstance)
        return null
    }

    fun handleEndLoopSnippet(snippetCmd: SnippetCmd.EVMSnippetCmd.LoopSnippet.EndLoopSnippet): CallTrace? {
        return ensureStackState(
            requirement = { it is CallInstance.LoopInstance.Start && it.id == snippetCmd.loopId },
            eventDescription = "start of loop ${snippetCmd.loopId}",
            allowedToPop = { it is CallInstance.BranchInstance.Start },
        )
    }

    fun handleStartIterSnippet(snippetCmd: SnippetCmd.EVMSnippetCmd.LoopSnippet.StartIter): CallTrace? {
        val snippetCallInstance = CallInstance.LoopInstance.Iteration(
            "Loop Iteration ${snippetCmd.iteration}",
            snippetCmd.iteration
        )
        Logger.regression {
            "Loop Iteration ${snippetCmd.iteration}"
        }
        callTracePush(snippetCallInstance)
        return null
    }

    fun handleEndIterSnippet(snippetCmd: SnippetCmd.EVMSnippetCmd.LoopSnippet.EndIter): CallTrace? {
        return ensureStackState(
            requirement = { it is CallInstance.LoopInstance.Iteration && it.iteration == snippetCmd.iteration },
            eventDescription = "start of loop iteration ${snippetCmd.iteration}",
            allowedToPop = { it is CallInstance.BranchInstance.Start },
        )
    }

    fun handleStartBranchSnippet(snippetCmd: SnippetCmd.EVMSnippetCmd.BranchSnippet.StartBranchSnippet): CallTrace? {
        val snippetCallInstance = CallInstance.BranchInstance.Start(snippetCmd.branchSource, snippetCmd.branchIndex)

        Logger.regression {
            snippetCallInstance.name
        }
        callTraceAppend(snippetCallInstance)

        if (!Config.flattenBranchesInCallTrace.get()) {
            currCallInstance = snippetCallInstance
        }

        return null
    }

    fun handleEndBranchSnippet(
        snippetCmd: SnippetCmd.EVMSnippetCmd.BranchSnippet.EndBranchSnippet,
        blockIndex: Int,
        cmdIdx: Int
    ): CallTrace? {
        if (currCallInstance.children.isEmpty()) {
            // check whether we want to display the branch in CallTrace or not, per Nurit's request to hide trivial branches.
            // trivial branches occur when there are no tac commands between start and end branch snippets,
            // e.g. as optimized away by require !lastReverted
            if (cmdIdx == 0 && blockIndex == 0) {
                return callTraceFailure { "invalid program, branch end is the first command in the first block." }
            }

            val prevCommand = if (cmdIdx > 0) {
                val blockId = blocks[blockIndex]
                val block = program.code[blockId] ?: return callTraceFailure { "unknown block $blockId." }
                block[cmdIdx - 1]
            } else {
                val blockId = blocks[blockIndex - 1]
                val block = program.code[blockId] ?: return callTraceFailure { "unknown block $blockId." }
                block.lastOrNull() ?: return callTraceFailure { "previous block $blockId is empty." }
            }

            prevCommand.maybeAnnotation(SNIPPET)?.let { prevSnippetCmd ->
                if (prevSnippetCmd is SnippetCmd.EVMSnippetCmd.BranchSnippet.StartBranchSnippet && prevSnippetCmd.branchIndex == snippetCmd.branchIndex) {
                    check(currCallInstance.parent?.children?.last() == currCallInstance) {
                        "Invalid state of call stack, current instance is not the last child of its parent."
                    }
                    currCallInstance.parent?.children?.removeLastOrNull()
                }
            }
        }

        val requirement: (CallInstance.ScopeInstance) -> Boolean =
            { it is CallInstance.BranchInstance.Start && it.id == snippetCmd.branchIndex }

        if (requirement(currCallInstance)) {
            callTracePop()
                ?: return invalidCallStack { "Try to access parent of $currCallInstance when looking for branch ${snippetCmd.branchIndex} end." }
            return null
        }

        var curr: CallInstance.ScopeInstance? = currCallInstance

        while (curr != null && !requirement(curr)) {
            curr = curr.parent
        }

        if (curr != null) {
            return invalidCallStack { "when branch ${snippetCmd.branchIndex} ends." }
        }

        logger.info {
            "Branch end of ${snippetCmd.branchIndex} did not meet a branch start at top of stack. " +
                "This is valid, as function return could have closed the branch already."
        }

        return null
    }

    fun handleLocalAssignmentSnippet(snippet: SnippetCmd.EVMSnippetCmd.SourceFinderSnippet.LocalAssignmentSnippet): Unit {
        Logger.regression {
            "Local assignment ${snippet.lhs}" // do not include the value, it is not stable
        }
        when (snippet.finderType) {
            // refer to https://www.notion.so/certora/Logging-Solidity-in-calltrace-135fe5c14fd380eb8453cfd3c8629449?pvs=4#135fe5c14fd3804fa47cfd0acc9b614c
            0 -> {
                callTraceAppend(CallInstance.LocalAssignmentInstance(
                    snippet.range,
                    sarifFormatter.fmt("{} {} {}",
                        FmtArg(snippet.lhs),
                        FmtArg.To,
                        CtfValue.buildOrUnknown(
                            model.valueAsTACValue(snippet.value),
                            EVMTypeDescriptor.UIntK(256) //xx pass better type info from solidity
                        )
                    )
                ))
            }
            1 -> {
                callTraceAppend(CallInstance.NonSpecificDeclInstance(snippet.range, snippet.lhs))
            }
            else -> {
                callTraceAppend(CallInstance.NonSpecificDefInstance(snippet.range, snippet.lhs))
            }
        }
    }

    fun handleHaltSnippet(snippet: SnippetCmd.EVMSnippetCmd.HaltSnippet): CallTrace? {
        // if we are not in an 'interesting' scope instance like a branch, loop, or invoke, don't show it.
        // this effectively may say "all scopes" where the halt snippet can actually appear in,
        // and we should consider whether the invoke scope is 'too obvious' and noisy.
        if (currCallInstance is CallInstance.BranchInstance || currCallInstance is CallInstance.LoopInstance || currCallInstance is CallInstance.InvokingInstance<*>) {
            val range = snippet.range
            val haltInstance = when (snippet) {
                is SnippetCmd.EVMSnippetCmd.HaltSnippet.Return -> CallInstance.HaltInstance.Return(range)
                is SnippetCmd.EVMSnippetCmd.HaltSnippet.Revert -> CallInstance.HaltInstance.Revert(range)
            }
            callTraceAppend(haltInstance)
        }

        return null
    }

    fun handleGhostAccessSnippet(sc: CVLSnippetCmd.GhostAccess) {
        val toolTip = when (sc) {
            is CVLSnippetCmd.GhostAssignment -> "value assigned to ghost"
            is CVLSnippetCmd.GhostRead -> "value read from ghost"
            is CVLSnippetCmd.SumGhostRead -> "value of sum"
            is CVLSnippetCmd.SumGhostUpdate -> "updated value of sum"
        }
        val accessedValueModel = model
            .valueAndPureCVLType(sc.accessed)
        val accessedValue = accessedValueModel
            .mapLeft { (tv, type) -> CtfValue.buildOrUnknown(tv, type, toolTip) }
            .leftOrElse { FmtArg.InlineSarif(CallTraceValueFormatter.unknown()) }

        val idp = sc
            .toInstantiatedDisplayPath(model)
            .mapLeft { it.toFormattedString(formatter) }
            .leftOrElse { Sarif.fromPlainStringUnchecked(CallTraceValueFormatter.UNKNOWN_VALUE) }

        val instance = CVLExpInstance(
            when (sc) {
                is CVLSnippetCmd.GhostRead -> sarifFormatter.fmt("Ghost read: {}{}{}", FmtArg(idp), FmtArg.To, accessedValue)
                is CVLSnippetCmd.SumGhostRead -> sarifFormatter.fmt("{}{}{}", FmtArg(idp), FmtArg.To, accessedValue)
                is CVLSnippetCmd.GhostAssignment -> sarifFormatter.fmt("Ghost assignment: {} = {}", FmtArg(idp), accessedValue)
                is CVLSnippetCmd.SumGhostUpdate -> sarifFormatter.fmt("{} = {}", FmtArg(idp), accessedValue)
            },
            sc.range as? CVLRange.Range,
            accessedValueModel.leftOrNull()?.first,
        )

        callTraceAppend(instance)

        globalState?.handleGhostAccessSnippet(sc)

        when (sc) {
            is CVLSnippetCmd.GhostRead,
            is CVLSnippetCmd.SumGhostRead -> Logger.regression { "CallTrace: ghost ${sc.name} was read in $currCallInstance" }
            is CVLSnippetCmd.GhostAssignment,
            is CVLSnippetCmd.SumGhostUpdate -> Logger.regression { "CallTrace: assignment to ${sc.name} in $currCallInstance" }
        }
    }

    private fun handleGhostHavocSnippet(
        sc: SnippetCmd.CVLSnippetCmd.GhostHavocSnippet,
        currBlock: NBId,
        idx: Int
    ): CallTrace? {
        val afterHavoc = CmdPointer(currBlock, idx + 1)
        globalState?.handleGhostHavoc(sc, afterHavoc)

        return null
    }

    private fun handleAllGhostsHavocSnippet(currBlock: NBId, idx: Int): CallTrace? {
        val afterHavoc = CmdPointer(currBlock, idx + 1)
        globalState?.handleAllGhostsHavoc(afterHavoc)

        val havocAllGhostsCallInstance = CallInstance.AllGhostsHavocInstance()
        Logger.regression {
            havocAllGhostsCallInstance.name
        }

        callTraceAppend(havocAllGhostsCallInstance)

        return null
    }

    fun handleCopyLoop(): CallTrace? {
        val snippetCallInstance = CallInstance.LoopInstance.CopyLoop()
        Logger.regression {
            snippetCallInstance.name
        }
        callTraceAppend(snippetCallInstance)

        return null
    }

    fun handleHavocBalanceSnippet(currBlock: NBId, idx: Int): CallTrace? {
        globalState?.handleHavocBalance(currBlock, idx)
        return null
    }

    fun handleStorageGlobalChangeSnippet(
        snippetCmd: SnippetCmd.EVMSnippetCmd.StorageGlobalChangeSnippet,
        currBlock: NBId,
        idx: Int
    ): CallTrace? {
        globalState?.handleStorageGlobalChanges(snippetCmd, currBlock, idx)
        return null
    }

    fun handleStorageDisplay(snippetCmd: SnippetCmd.CVLSnippetCmd.StorageDisplay): CallTrace? {
        globalState?.computeGlobalState(snippetCmd.sym, formatter = formatter)?.let(::callTraceAppend)
        return null
    }

    fun handleAssignmentSnippet(snippetCmd: SnippetCmd.EVMSnippetCmd.ContractSourceSnippet.AssignmentSnippet): CallTrace? {
        val label = with(snippetCmd.parse) {
            val typ = data.typ ?: CVLType.PureCVLType.Primitive.UIntK(256) //TODO propagate the type from Solidity AST

            val currentValue =
                CallTraceValue.cvlCtfValueOrUnknown(model.valueAsTACValue(snippetCmd.lhs), typ)
                    .toSarif(formatter, "current value")
                    .flatten()

            val fileName = originalSource.fileName
            val content = originalSource.content.condense()

            Logger.regression {
                val dummy = "*"
                if (data.typ != null) {
                    "Assignment: ${data.name} (type: ${data.typ}) = $dummy"
                } else {
                    "Assignment: ${data.name} = $dummy"
                }
            }

            "$fileName:${originalSource.lineNumber}:$content /* ${data.name} = $currentValue */"
        }

        val range = snippetCmd.parse.originalSource.range

        callTraceAppend(CallInstance.ContractSourceInstance.Assignment(label, range))
        return null
    }

    fun handleEVMFunctionReturnWrite(snippetCmd: SnippetCmd.EVMSnippetCmd.EVMFunctionReturnWrite): CallTrace? {
        val movementCallIndex = currCallInstance.ancestorOfType<SolidityInvokeInstance>(
            // maybe overprotective, we could have other solidity calls, we don't want to blindly take a different ancestor of the same type
            allowedToSkip = { it is CallInstance.BranchInstance || it is CallInstance.LoopInstance }
        )?.callIndex

        if (movementCallIndex != null && callInputsAndOutputs.externalCall(movementCallIndex) != null) {
            val movement = snippetCmd.returndataMovement(movementCallIndex)
            callInputsAndOutputs.registerReturndataMovement(movement, movementCallIndex)
        }
        return null
    }

    /**
     * Creates a [CallInstance] for [snippetCmd] and adds it to the CallHierarchy starting at [callHierarchyRoot].
     */
    fun handleAssertSnippet(snippetCmd: AssertSnippet<*>, cmd: TACCmd.Simple, currBlock: NBId, idx: Int): CallTrace? {
        val assertCondValuation = model.valueAsBoolean(snippetCmd.assertCond)
        val (assertViolationOrErrorMsg, assertHasPassedOrNull) = assertCondValuation.toValue(
            l = { assertCondValue: Boolean ->
                if (assertCondValue) {
                    "passed" to true
                } else {
                    "failed" to false
                }
            },
            r = { cexResolvingFailure ->
                // We failed to get the value of the assert condition.
                // Therefore, we cannot know whether the enclosed assert
                // has failed or not. In this case, we die
                val errorMsg =
                    cexResolvingFailure(snippetCmd.assertCond)
                logger.error { errorMsg }
                // The [ScopeSnippet] guarantees the CallTrace construction
                // to fail later when it reaches the enclosed assert command
                errorMsg to null
            }
        )
        val (assertSnippetCallInstance, assertCheckMsg) = when (snippetCmd) {
            is SnippetCmd.CVLSnippetCmd.DivZero -> {
                CallInstance.DivZeroInstance(
                    snippetCmd.assertCmdLabel,
                    snippetCmd.range as? CVLRange.Range,
                ) to "Check division by zero for ${snippetCmd.assertCmdLabel}: $assertViolationOrErrorMsg"
            }

            is SnippetCmd.CVLSnippetCmd.AssertCast -> {
                CallInstance.CastCheckInstance(
                    "assert-cast check $assertViolationOrErrorMsg",
                    snippetCmd.range as? CVLRange.Range,
                ) to "assert-cast check: $assertViolationOrErrorMsg"
            }

            is SnippetCmd.EVMSnippetCmd.LoopSnippet.AssertUnwindCond -> {
                CallInstance.LoopInstance.AssertUnwindCond(
                    "Assert 'loop has terminated' $assertViolationOrErrorMsg"
                ) to "Assert 'loop has terminated' $assertViolationOrErrorMsg"
            }

            is SnippetCmd.CVLSnippetCmd.ViewReentrancyAssert -> {
                CallInstance.ViewReentrancyInstance(snippetCmd.msg, snippetCmd.range) to snippetCmd.msg
            }
        }
        if (assertHasPassedOrNull != true || snippetCmd.displayIfPassed) {
            callTraceAppend(assertSnippetCallInstance)
            if (snippetCmd is WithParseTree) {
                try {
                    evaldCVLExpBuilder.materializeCVLBoolCondExpInfo(
                        snippetCmd.cvlExpOutSym,
                        assertSnippetCallInstance
                    )
                } catch (e: IllegalStateException) {
                    logger.error(e) { "Failed to generate a parse tree for an expression in an assert statement ($cmd" }
                }
            }
        }
        return if (assertHasPassedOrNull != null) {
            Logger.regression { assertCheckMsg }
            if (!assertHasPassedOrNull) {
                val violatedAssert = LTACCmd(CmdPointer(currBlock, idx), cmd)
                ViolationFound(callHierarchyRoot, violatedAssert)
            } else {
                null
            }
        } else {
            null
        }
    }

    fun handleIfStart(snippetCmd: SnippetCmd.CVLSnippetCmd.IfStart) {
        val instance = CallInstance.CVLIf(
            CVLReportLabel.Exp(snippetCmd.cond).toString(),
            snippetCmd.id,
            snippetCmd.range as? CVLRange.Range,
        )
        callTracePush(instance)
        evaldCVLExpBuilder.materializeCVLBoolCondExpInfo(snippetCmd.condVar, currCallInstance)
        Logger.regression { "'If condition' CallInstance was added as the child of ${currCallInstance.name}" }
    }

    fun handleBranchStart(snippetCmd: SnippetCmd.CVLSnippetCmd.BranchStart) {
        val instance = CallInstance.CVLBranch(snippetCmd.kind, snippetCmd.id, snippetCmd.range as? CVLRange.Range)
        callTracePush(instance)

    }

    fun handleEVMFunctionInvCVLValueTypeArg(snippetCmd: SnippetCmd.CVLSnippetCmd.EVMFunctionInvCVLValueTypeArg): CallTrace? {
        val movementCallIndex = (currCallInstance as? SolidityInvokeInstance)?.callIndex

        if (movementCallIndex != null && callInputsAndOutputs.externalCall(movementCallIndex) != null) {
            val movement = snippetCmd.calldataMovement(movementCallIndex)
            callInputsAndOutputs.registerCalldataMovement(movement, movementCallIndex)
        }
        return null
    }

    fun handleCVLFunctionStart(snippetCmd: SnippetCmd.CVLSnippetCmd.CVLFunctionStart): CallTrace? {
        val cvlFunctionInstance =
            CallInstance.InvokingInstance.CVLFunctionInstance(
                snippetCmd.callIndex,
                snippetCmd.name,
                snippetCmd.range.tryAs(),
                formatter
            )

        callInputsAndOutputs.initCVLCall(snippetCmd.callIndex)
        callTracePush(cvlFunctionInstance)

        return null
    }

    fun handleCVLFunctionEnd(snippetCmd: SnippetCmd.CVLSnippetCmd.CVLFunctionEnd): CallTrace? {
        val currentFunction = currCallInstance.ancestorOfType<CallInstance.InvokingInstance.CVLFunctionInstance>()
        return if (currentFunction != null && currentFunction.callIndex == snippetCmd.callIndex) {
            Logger.regression {
                "End of cvl function $currentFunction returns ${currentFunction.returnValuesToString()}"
            }
            this.callTracePop()!! // cannot fail - if we got here, call tree is not empty
            callInputsAndOutputs.finalizeCVLCall(currentFunction)
            null
        } else {
            val actual = if (currentFunction != null) {
                "got function ${currentFunction.name} (id = ${currentFunction.callIndex})"
            } else {
                "not inside function"
            }
            invalidCallStack { "expected current cvl function to be ${snippetCmd.name} (id = ${snippetCmd.callIndex}), but $actual" }
        }
    }

    fun handleCVLFunctionArg(snippetCmd: SnippetCmd.CVLSnippetCmd.CVLArg): CallTrace? {
        currCallInstance.ancestorOfType<CallInstance.InvokingInstance.PureCVLInvokingInstance>()
            ?: return invalidCallStack { "Missing start of cvl function ${snippetCmd.callIndex} for argument ${snippetCmd.param}" }

        when (snippetCmd) {
            is SnippetCmd.CVLSnippetCmd.CVLArg.AnyArg -> {
                return callTraceFailure { "invalid CallTrace, AnyArg should have been changed during compilation." }
            }

            is SnippetCmd.CVLSnippetCmd.CVLArg.PrimitiveArg -> {
                callInputsAndOutputs.addCVLFunctionParam(
                    snippetCmd.callIndex,
                    snippetCmd.index,
                    snippetCmd.param,
                    snippetCmd.sym
                )
            }

            is SnippetCmd.CVLSnippetCmd.CVLArg.ArrayArg -> {
                callInputsAndOutputs.addCVLFunctionArrayParam(
                    snippetCmd.callIndex,
                    snippetCmd.index,
                    snippetCmd.param,
                    snippetCmd.len
                )
            }

            is SnippetCmd.CVLSnippetCmd.CVLArg.BlockchainStateArg -> {
                callInputsAndOutputs.addCVLFunctionParam(snippetCmd.callIndex, snippetCmd.index, snippetCmd.param, null)
            }

            is SnippetCmd.CVLSnippetCmd.CVLArg.StructArg -> {
                callInputsAndOutputs.addCVLFunctionStructParam(
                    snippetCmd.callIndex,
                    snippetCmd.index,
                    snippetCmd.param,
                    snippetCmd.symbols
                )
            }
        }
        return null
    }

    fun handleCVLFunctionRet(snippetCmd: SnippetCmd.CVLSnippetCmd.CVLRet): CallTrace? {
        currCallInstance.ancestorOfType<CallInstance.InvokingInstance.CVLFunctionInstance>()
            ?: return invalidCallStack { "Missing start of cvl function ${snippetCmd.callIndex} for return value ${snippetCmd.index}" }

        when (snippetCmd) {
            is SnippetCmd.CVLSnippetCmd.CVLRet.AnyRet -> {
                return callTraceFailure { "invalid CallTrace, AnyRet should have been changed during compilation." }
            }

            is SnippetCmd.CVLSnippetCmd.CVLRet.PrimitiveRet -> {
                callInputsAndOutputs.addCVLFunctionReturnValue(
                    snippetCmd.callIndex,
                    snippetCmd.index,
                    snippetCmd.type,
                    snippetCmd.sym
                )

                materializeCVLBoolCondExpInfoWithParent(snippetCmd.sym, "return")
            }

            is SnippetCmd.CVLSnippetCmd.CVLRet.ArrayRet,
            is SnippetCmd.CVLSnippetCmd.CVLRet.BlockchainStateRet,
            is SnippetCmd.CVLSnippetCmd.CVLRet.StructRet -> {
                callInputsAndOutputs.addCVLFunctionReturnValue(
                    snippetCmd.callIndex,
                    snippetCmd.index,
                    snippetCmd.type,
                    null
                )

                /** since currently we can't generate a parse tree for these cases, default to printing the original expression */
                val instance = CallInstance.LabelInstance(snippetCmd.label)
                currCallInstance.addChild(instance)
            }
        }
        return null
    }

    fun handleStorageComparison(snippetCmd: SnippetCmd.CVLSnippetCmd.StorageComparison): CallTrace? {
        val definitelyFailed = model.valueAsBoolean(snippetCmd.resultSymbol).toValue(
            l = { !it },
            r = { resolverFailure ->
                val errorMsg = resolverFailure.invoke(
                    snippetCmd.resultSymbol
                )
                logger.error(errorMsg)
                false
            })

        if (!definitelyFailed) {
            return null
        }

        val result = sarifForStorageLocation(snippetCmd, model, formatter, scene)
        val where = when (result) {
            is Either.Left -> result.d
            is Either.Right -> return logger.warnAndNull { result.d }
        }

        val inst = CallInstance.StorageCounterExampleInstance(
            sarifFormatter.fmt("Found different values {}:", FmtArg(where))
        )

        val mv1 = model.valueAsTACValue(snippetCmd.p1.second)
        val mv2 = model.valueAsTACValue(snippetCmd.p2.second)

        fun wrapWithData(type: VMTypeDescriptor) =
            CtfValue.buildOrUnknown(mv1, type, "value at storage location") to
                CtfValue.buildOrUnknown(mv2, type, "value at storage location")
        fun wrapWithData(type: CVLType.PureCVLType) =
            CtfValue.buildOrUnknown(mv1, type, "value at storage location") to
                CtfValue.buildOrUnknown(mv2, type, "value at storage location")

        val (value1, value2) = when (snippetCmd) {
            is SnippetCmd.CVLSnippetCmd.ScalarStorageComparison ->
                snippetCmd.typeValue?.let { wrapWithData(it) }

            is SnippetCmd.CVLSnippetCmd.StorageWitnessComparison -> when (snippetCmd.basis) {
                StorageBasis.Balances, StorageBasis.ExternalCodesizes ->
                    wrapWithData(EVMTypeDescriptor.UIntK(256))
                is StorageBasis.ContractClass ->
                    snippetCmd.typeValue?.let { wrapWithData(it) }
            }

            is SnippetCmd.CVLSnippetCmd.GhostWitnessComparison -> wrapWithData(snippetCmd.basis.resultType)
            is SnippetCmd.CVLSnippetCmd.ScalarGhostComparison -> wrapWithData(snippetCmd.basis.resultType)
        } ?: return logger.warnAndNull { "Could not get type for snippet $snippetCmd" }

        val leftExample = CallInstance.StorageCounterExampleInstance(
            sarifFormatter.fmt("In ${snippetCmd.p1.first}: {}", value1)
        )
        val rightExample = CallInstance.StorageCounterExampleInstance(
            sarifFormatter.fmt("In ${snippetCmd.p2.first}: {}", value2)
        )
        callTraceAppend(inst)
        inst.addChild(leftExample)
        inst.addChild(rightExample)
        return null
    }

    // solana
    fun handleSolanaCexPrintValues(snippetCmd: SnippetCmd.SolanaSnippetCmd.CexPrintValues, stmt: TACCmd.Simple.AnnotationCmd): CallTrace? {
        val range = consumeAttachedRangeOrResolve(stmt)
        val formattedList = snippetCmd.symbols.map { sym ->
            CallTraceValue.cvlCtfValueOrUnknown(
                model.valueAsTACValue(sym),
                CVLType.PureCVLType.Primitive.UIntK(256)
            ).toSarif(formatter, tooltip = "value")
        }
        val sarif = sarifFormatter.fmt(
            "${snippetCmd.displayMessage}: " + List(formattedList.size){_ -> "{}"}.joinToString(", "),
            *formattedList.map { FmtArg(it) }.toTypedArray()
        )
        callTraceAppend(CallInstance.SolanaCexPrintValues(sarif, range))
        return null
    }

    fun handleSolanaCexPrintLocation(snippetCmd: SnippetCmd.SolanaSnippetCmd.CexPrintLocation): CallTrace? {
        val range = filepathAndLineNumberToRange(snippetCmd.filepath, snippetCmd.lineNumber)
        val tag = "${snippetCmd.filepath}:${snippetCmd.lineNumber}"
        callTraceAppend(CallInstance.SolanaCexPrintTag(tag, range))
        return null
    }

    fun handleSolanaCexAttachLocation(snippetCmd: SnippetCmd.SolanaSnippetCmd.CexAttachLocation): CallTrace? {
        lastRangeSetByAttachLocationCmd = filepathAndLineNumberToRange(snippetCmd.filepath, snippetCmd.lineNumber)
        return null
    }

    /** Converts a filepath and a line number to a range. If the file is not in the sources dir, returns [null]. */
    private fun filepathAndLineNumberToRange(filepath: String, lineNumber: UInt): CVLRange.Range? {
        val fileInSourcesDir = File(Config.prependSourcesDir(filepath))
        return if (fileInSourcesDir.exists()) {
            val cvlRangeLineNumber = lineNumber - 1U
            // We do not have column information.
            val cvlRangeColNumber = 0U
            val sourcePositionStart = SourcePosition(cvlRangeLineNumber, cvlRangeColNumber)
            // Since we do not have end range information, we just assume it is the next line.
            val sourcePositionEnd = SourcePosition(cvlRangeLineNumber + 1U, cvlRangeColNumber)
            CVLRange.Range(filepath, sourcePositionStart, sourcePositionEnd)
        } else {
            sbfLogger.warn {
                "file '$fileInSourcesDir' does not exist: jump to source information will not be available"
            }
            null
        }
    }

    fun handleSolanaCexPrintTag(snippetCmd: SnippetCmd.SolanaSnippetCmd.CexPrintTag, stmt: TACCmd.Simple.AnnotationCmd): CallTrace? {
        val range = consumeAttachedRangeOrResolve(stmt)
        val instance = CallInstance.SolanaCexPrintTag(
            name = snippetCmd.displayMessage,
            range = range
        )
        callTraceAppend(instance)
        return null
    }

    /**
     * If [lastRangeSetByAttachLocationCmd] is set, returns its value and sets the variable to [null].
     * If [lastRangeSetByAttachLocationCmd] is [null], reads the range from the debug information from the executable.
     */
    private fun consumeAttachedRangeOrResolve(stmt: TACCmd.Simple.AnnotationCmd): CVLRange.Range? {
        val range = lastRangeSetByAttachLocationCmd ?: sbfAddressToRangeWithHeuristic(stmt)
        lastRangeSetByAttachLocationCmd = null
        return range
    }

    fun handleSolanaFunctionStart(annot: SbfInlinedFuncStartAnnotation): CallTrace? {
        val newInstance = CallInstance.InvokingInstance.SolanaFunctionInstance(
            "${annot.name}(...)",
            annot.id
        )
        callTracePush(newInstance)
        return null
    }

    fun handleSolanaFunctionEnd(annot: SbfInlinedFuncEndAnnotation): CallTrace? {
        return ensureStackState(
            requirement = { it is CallInstance.InvokingInstance.SolanaFunctionInstance && it.callIndex == annot.id },
            eventDescription = "start of solana function (id = ${annot.id})"
        )
    }

    fun handleSolanaExternalCall(snippetCmd: SnippetCmd.SolanaSnippetCmd.ExternalCall): CallTrace? {
        val formattedList = snippetCmd.symbols.map { sym ->
            CallTraceValue.cvlCtfValueOrUnknown(
                model.valueAsTACValue(sym),
                CVLType.PureCVLType.Primitive.UIntK(256)
            ).toSarif(formatter, tooltip = "value")
        }
        val sarif =
            sarifFormatter.fmt(
                "${snippetCmd.displayMessage}: " + List(formattedList.size){ _ -> "{}"}
                    .joinToString(", "),
                *formattedList.map { FmtArg(it) }.toTypedArray()
            )
        callTraceAppend(CallInstance.SolanaExternalCall(sarif))
        return null
    }

    fun handleSolanaUserAssert(snippetCmd: SnippetCmd.SolanaSnippetCmd.Assert, stmt: TACCmd.Simple.AnnotationCmd): CallTrace? {
        val range = consumeAttachedRangeOrResolve(stmt)
        val v = model.valueAsBoolean(snippetCmd.symbol).leftOrNull()
        val msg:String = if (v != null) {
            if (v) {
                "assert OK"
            } else {
                "assert FAIL"
            }
        } else {
           "assert UNKNOWN"
        }
        callTraceAppend(CallInstance.SolanaUserAssert(msg, range))
        return null
    }

    // wasm
    fun handleWasmFunctionStart(annot: StraightLine.InlinedFuncStartAnnotation.TAC) {
        val newInstance = CallInstance.InvokingInstance.WasmFunctionInstance(
            "function start: ${annot.funcName} ${ite(annot.range != null, "in ${annot.range}","")}",
            annot.funcName)
        callTracePush(newInstance)
    }

    fun handleWasmFunctionEnd(annot: StraightLine.InlinedFuncEndAnnotation.TAC): CallTrace? {
        return ensureStackState(
            requirement = { it is CallInstance.InvokingInstance.WasmFunctionInstance && it.funcName == annot.funcName },
            eventDescription = "start of wasm function ${annot.funcName}"
        )
    }

    fun handleWasmUserAssume(name: String) {
        callTraceAppend(CallInstance.WasmUserAssume("user assume: $name", null))
    }

    fun handleWasmCalltracePrint(annot: StraightLine.CexPrintValues) {
        callTraceAppend(CallInstance.WasmUserAssume("${annot.tag}: ${annot.symbols.map { v -> model.valueAsTACValue(v) }.joinToString(",")}", null))
    }

    fun handleWasmUserAssert(name: String) {
        callTraceAppend(CallInstance.WasmUserAssert("user assert: $name", null))
    }

    fun handleInlinedHook(cmd: SnippetCmd.CVLSnippetCmd.InlinedHook, labelId: Int): CallTrace? {
        val hookHeader = cmd.cvlPattern.toHookApplicationHeader(labelId)

        val substitutions = cmd.substitutions.entries.sortedBy { it.key.name }

        if (substitutions.isNotEmpty()) {
            val paramExplanationsHeader = CallInstance.LabelInstance("With parameters:")
            hookHeader.addChild(paramExplanationsHeader)

            for ((subbedParam, hook) in substitutions) {
                val subName = subbedParam.name
                val hookValue = model.instantiate(hook)?.value
                val hookDescription = hookValue?.let { "0x" + it.toString(16) } ?: "?"
                val labelInstance = CallInstance.LabelInstance("$subName = $hookDescription")
                paramExplanationsHeader.addChild(labelInstance)
            }
        }

        callTracePush(hookHeader)
        return null
    }

    /**
     * this function checks this section for a [SnippetCmd.CVLSnippetCmd.InlinedHook] annotation,
     * because we merge these with the start label of the section.
     *
     * we define a "section" as the commands between a [CVL_LABEL_START] and a [CVL_LABEL_END].
     * we expect this section to be entirely contained within a single block.
     */
    fun findInlinedHookInSection(ptr: CmdPointer): SnippetCmd.CVLSnippetCmd.InlinedHook? {
        return graph
            .iterateBlock(ptr, excludeStart = true)
            .mapNotNull { it.cmd as? TACCmd.Simple.AnnotationCmd }
            .takeWhile { it.annot.k != CVL_LABEL_START && it.annot.k != CVL_LABEL_END }
            .firstMapped { it.annot.v as? SnippetCmd.CVLSnippetCmd.InlinedHook }
    }


    /** generates the call trace by iterating over the reachable commands of [program] in topological order. */
    fun generate(): CallTrace {
        globalState?.computeGlobalState(formatter = formatter)?.let(::callTraceAppend)

        blocks.forEachIndexed { blockIdx, currBlock ->
            val block = program.code[currBlock] ?: return callTraceFailure { "unknown block $currBlock." }
            block.forEachIndexed inner@{ idx, stmt ->
                printer?.visit(LTACCmd(CmdPointer(currBlock, idx), stmt))
                if (stmt.meta.containsKey(TACMeta.IGNORE_IN_CALLTRACE)) {
                    return@inner
                }

                /**
                 * if a handler function may return a non-null value,
                 * do _not_ silently ignore the return value!
                 * instead, return it as the value of the `when` branch.
                 *
                 * otherwise, execution of [generate] will not stop
                 * at the end of that handler function.
                 */
                val calltrace: CallTrace? = when (stmt) {
                    is TACCmd.Simple.AssigningCmd -> {
                        handleAssigningCmd(stmt)
                    }

                    is TACCmd.Simple.AssumeCmd -> {
                        handleAssumeCmd(stmt)
                    }

                    is TACCmd.Simple.AssertCmd -> {
                        handleAssert(stmt, currBlock, idx)
                    }

                    is TACCmd.Simple.AnnotationCmd -> {
                        val (meta, value) = stmt.annot
                        when (meta) {
                            CVL_LABEL_START -> {
                                val label = value as CVLReportLabel
                                val labelId = stmt.meta[CVL_LABEL_START_ID]
                                    ?: return callTraceFailure { "missing label id for start label: `$label`" }
                                val ptr = CmdPointer(currBlock, idx)
                                val inlinedHook = findInlinedHookInSection(ptr)

                                if (inlinedHook != null) {
                                    // we handle this here _instead_ of the start label.
                                    // then later on, when we reach this inlined hook annotation,
                                    // we skip it.
                                    handleInlinedHook(inlinedHook, labelId)
                                } else {
                                    handleCvlLabelStart(label, labelId)
                                }
                            }

                            CVL_LABEL_END -> {
                                handleCvlLabelEnd(value as Int)
                            }

                            SNIPPET -> {
                                when (val snippetCmd = value as SnippetCmd) {
                                    is AssertSnippet<*> -> {
                                        handleAssertSnippet(snippetCmd, stmt, currBlock, idx)
                                    }

                                    is SnippetCmd.CVLSnippetCmd.IfStart -> {
                                        handleIfStart(snippetCmd)
                                        null
                                    }

                                    is SnippetCmd.CVLSnippetCmd.BranchStart -> {
                                        handleBranchStart(snippetCmd)
                                        null
                                    }

                                    is SnippetCmd.CVLSnippetCmd.EVMFunctionInvCVLValueTypeArg -> {
                                        handleEVMFunctionInvCVLValueTypeArg(snippetCmd)
                                    }

                                    is SnippetCmd.CVLSnippetCmd.StorageDisplay -> {
                                        handleStorageDisplay(snippetCmd)
                                    }

                                    is SnippetCmd.EVMSnippetCmd.StorageSnippet -> {
                                        handleStorageSnippet(snippetCmd)
                                    }

                                    is SnippetCmd.EVMSnippetCmd.RawStorageAccess -> {
                                        handleRawStorageSnippet(snippetCmd)
                                        null
                                    }

                                    is SnippetCmd.EVMSnippetCmd.ReadBalanceSnippet -> {
                                        handleBalanceSnippet(snippetCmd)
                                    }

                                    SnippetCmd.EVMSnippetCmd.HavocBalanceSnippet -> {
                                        handleHavocBalanceSnippet(currBlock, idx)
                                    }

                                    is SnippetCmd.EVMSnippetCmd.TransferSnippet -> {
                                        handleTransferSnippet(snippetCmd)
                                    }

                                    is SnippetCmd.EVMSnippetCmd.StorageGlobalChangeSnippet -> {
                                        handleStorageGlobalChangeSnippet(snippetCmd, currBlock, idx)
                                    }

                                    is SnippetCmd.EVMSnippetCmd.ContractSourceSnippet.AssignmentSnippet -> {
                                        handleAssignmentSnippet(snippetCmd)
                                    }

                                    is SnippetCmd.EVMSnippetCmd.EVMFunctionReturnWrite -> {
                                        handleEVMFunctionReturnWrite(snippetCmd)
                                    }

                                    is SnippetCmd.CVLSnippetCmd.StorageComparison -> {
                                        handleStorageComparison(snippetCmd)
                                    }

                                    is SnippetCmd.EVMSnippetCmd.LoopSnippet.StartLoopSnippet -> handleStartLoopSnippet(
                                        snippetCmd
                                    )

                                    is SnippetCmd.EVMSnippetCmd.LoopSnippet.EndIter -> handleEndIterSnippet(snippetCmd)
                                    is SnippetCmd.EVMSnippetCmd.LoopSnippet.StartIter -> handleStartIterSnippet(
                                        snippetCmd
                                    )

                                    is SnippetCmd.EVMSnippetCmd.LoopSnippet.EndLoopSnippet -> handleEndLoopSnippet(
                                        snippetCmd
                                    )

                                    SnippetCmd.EVMSnippetCmd.LoopSnippet.CopyLoop -> handleCopyLoop()
                                    is SnippetCmd.EVMSnippetCmd.BranchSnippet.StartBranchSnippet -> handleStartBranchSnippet(
                                        snippetCmd
                                    )

                                    is SnippetCmd.EVMSnippetCmd.BranchSnippet.EndBranchSnippet -> handleEndBranchSnippet(
                                        snippetCmd,
                                        blockIdx,
                                        idx
                                    )

                                    is SnippetCmd.EVMSnippetCmd.SourceFinderSnippet.LocalAssignmentSnippet -> {
                                        handleLocalAssignmentSnippet(
                                            snippetCmd
                                        )
                                        null
                                    }
                                    is SnippetCmd.EVMSnippetCmd.HaltSnippet -> handleHaltSnippet(snippetCmd)
                                    is SnippetCmd.CVLSnippetCmd.CVLFunctionStart -> {
                                        handleCVLFunctionStart(snippetCmd)
                                    }

                                    is SnippetCmd.CVLSnippetCmd.CVLFunctionEnd -> {
                                        handleCVLFunctionEnd(snippetCmd)
                                    }

                                    is SnippetCmd.CVLSnippetCmd.CVLArg -> {
                                        handleCVLFunctionArg(snippetCmd)
                                    }

                                    is SnippetCmd.CVLSnippetCmd.CVLRet -> {
                                        handleCVLFunctionRet(snippetCmd)
                                    }

                                    is SnippetCmd.CVLSnippetCmd.GhostRead -> {
                                        handleGhostAccessSnippet(snippetCmd)
                                        null
                                    }

                                    is SnippetCmd.CVLSnippetCmd.GhostAssignment -> {
                                        handleGhostAccessSnippet(snippetCmd)
                                        null
                                    }

                                    is SnippetCmd.CVLSnippetCmd.GhostHavocSnippet -> {
                                        handleGhostHavocSnippet(snippetCmd, currBlock, idx)
                                    }

                                    is SnippetCmd.CVLSnippetCmd.HavocAllGhostsSnippet -> {
                                        handleAllGhostsHavocSnippet(currBlock, idx)
                                    }

                                    is CVLSnippetCmd.SumGhostRead -> {
                                        handleGhostAccessSnippet(snippetCmd)
                                        null
                                    }

                                    is CVLSnippetCmd.SumGhostUpdate -> {
                                        handleGhostAccessSnippet(snippetCmd)
                                        null
                                    }
                                    is SnippetCmd.CVLSnippetCmd.InlinedHook -> {
                                        /**
                                         * we _do not_ handle this here. we handled this earlier,
                                         * when we reached the [CVL_LABEL_START] above this.
                                         *
                                         * yes, that's kinda weird. see [findInlinedHookInSection].
                                         */
                                        null
                                    }

                                    // solana
                                    is SnippetCmd.SolanaSnippetCmd.CexPrintValues -> {
                                        handleSolanaCexPrintValues(snippetCmd, stmt)
                                    }

                                    is SnippetCmd.SolanaSnippetCmd.CexPrintLocation -> {
                                        handleSolanaCexPrintLocation(snippetCmd)
                                    }

                                    is SnippetCmd.SolanaSnippetCmd.CexAttachLocation -> {
                                        handleSolanaCexAttachLocation(snippetCmd)
                                    }

                                    is SnippetCmd.SolanaSnippetCmd.CexPrintTag -> {
                                        handleSolanaCexPrintTag(snippetCmd, stmt)
                                    }

                                    is SnippetCmd.SolanaSnippetCmd.ExternalCall -> {
                                        handleSolanaExternalCall(snippetCmd)
                                    }

                                    is SnippetCmd.SolanaSnippetCmd.Assert -> {
                                        handleSolanaUserAssert(snippetCmd, stmt)
                                    }

                                    SnippetCmd.SnippetCreationDisabled -> {
                                        null
                                    }
                                }
                            }

                            /*
                               Some exit annotation are missing corresponding start annotation, and some start annotation are missing
                               corresponding exit annotations. Given an exit annotation, if we find a corresponding start annotation,
                               we pop from the stack until we are getting to the (promised exist) start annotation, and continue
                               to build the callTrace (basically, skip all the things between them). Otherwise, we just ignore,
                               and throw a warning.
                             */
                            INTERNAL_FUNC_START -> {
                                handleInternalFuncStart(value as InternalFuncStartAnnotation)
                            }

                            INTERNAL_FUNC_EXIT -> {
                                handleInternalFuncExit(value as InternalFuncExitAnnotation)
                            }

                            STACK_PUSH -> {
                                handleStackPush(value as Inliner.CallStack.PushRecord)
                            }

                            STACK_POP -> {
                                handleStackPop(value as Inliner.CallStack.PopRecord)
                            }

                            TACMeta.REVERT_PATH -> {
                                handleRevertPath(stmt, currBlock, idx)
                            }

                            TACMeta.THROW_PATH -> {
                                handleThrowPath()
                            }

                            SummaryStack.START_EXTERNAL_SUMMARY, SummaryStack.START_INTERNAL_SUMMARY -> {
                                handleSummaryStart(value as SummaryStack.SummaryStart, currBlock, idx)
                            }

                            SummaryStack.END_EXTERNAL_SUMMARY -> {
                                handleExternalSummaryEnd(value as SummaryStack.SummaryEnd.External)
                            }

                            SummaryStack.END_INTERNAL_SUMMARY -> {
                                handleInternalSummaryEnd(value as SummaryStack.SummaryEnd.Internal)
                            }

                            // solana
                            SBF_INLINED_FUNCTION_START -> {
                                handleSolanaFunctionStart(value as SbfInlinedFuncStartAnnotation)
                            }

                            SBF_INLINED_FUNCTION_END -> {
                                handleSolanaFunctionEnd(value as SbfInlinedFuncEndAnnotation)
                            }

                            // wasm
                            WASM_INLINED_FUNC_START -> {
                                handleWasmFunctionStart(value as StraightLine.InlinedFuncStartAnnotation.TAC)
                                null
                            }

                            WASM_CALLTRACE_PRINT -> {
                                handleWasmCalltracePrint(value as StraightLine.CexPrintValues)
                                null
                            }

                            WASM_INLINED_FUNC_END -> {
                                handleWasmFunctionEnd(value as StraightLine.InlinedFuncEndAnnotation.TAC)
                            }

                            WASM_USER_ASSUME -> {
                                handleWasmUserAssume(value as String)
                                null
                            }

                            WASM_USER_ASSERT -> {
                                handleWasmUserAssert(value as String)
                                null
                            }

                            else -> null
                        }
                    }

                    else -> null
                }

                if (calltrace != null) {
                    // finalize all open calls
                    // the failing assert may be before their end, and without this we won't see their arguments and return values.
                    var currInstance: CallInstance.ScopeInstance? = currCallInstance
                    while (currInstance != null) {
                        when (val inst = currInstance) {
                            is CallInstance.InvokingInstance.CVLFunctionInstance -> callInputsAndOutputs.finalizeCVLCall(
                                inst
                            )

                            is SolidityInvokeInstance.External -> callInputsAndOutputs.finalizeExternalCall(inst)
                            else -> {}
                        }
                        currInstance = currInstance.parent
                    }
                    return calltrace
                }
            }
        }
        return callTraceFailure { "did not reach a violated assert command in $ruleName" }
    }

    /**
     * Converts an SBF address from the metadata of the given TAC command to a range.
     * Returns [null] if the SBF metadata is not present or if it is not possible to resolve the range information.
     * Tries to resolve the inlined frames associated also to previous SBF addresses until [address - windowSize].
     */
    private fun sbfAddressToRangeWithHeuristic(
        stmt: TACCmd.Simple.AnnotationCmd,
        windowSize: UShort = 80U
    ): CVLRange.Range? {
        return stmt.meta[SBF_ADDRESS]?.let { address ->
            val uLongAddress = address.toULong()
            // Consider address, address - 8, address - 16, ..., address - (windowSize + 8)
            val addresses: MutableList<ULong> = mutableListOf()
            var nextAddress = uLongAddress
            // The first condition is to check the absence of underflows.
            while (uLongAddress <= nextAddress && uLongAddress - nextAddress <= windowSize) {
                addresses.add(nextAddress)
                nextAddress -= 8U
            }
            val rangesMap = InlinedFramesInfo.getInlinedFramesInProjectFiles(addresses)
            // Iterate over the addresses: address, address - 8, address - 16, ...
            // The first address that is associated with non-null range information will be the returned address.
            for (addr in addresses) {
                rangesMap[addr]?.let { ranges ->
                    ranges.firstOrNull { range ->
                        return range
                    }
                }
            }
            return null
        }
    }
}

/**
 * this class is constructed using [invoke].
 * contains the [callHierarchyRoot] of a [IRule] which is the result of running [CallTraceGenerator],
 * up to the point where [CallTraceGenerator] returned.
 *
 * if a violated assert is found (as is expected), the [ViolationFound] variant will contain this violation.
 *
 * otherwise, if an exception is encountered during call trace generation, or if no violation is found,
 * the [Failure] variant will be returned, containing the exception.
 */
sealed class CallTrace {
    abstract val callHierarchyRoot: CVLRootInstance
    abstract val alertReport: RuleAlertReport.Single<*>?

    /** For usage in JUnit tests (for now at least). */
    val formatter get() = callHierarchyRoot.formatter

    data class ViolationFound(override val callHierarchyRoot: CVLRootInstance, val violatedAssert: LTACCmd) : CallTrace() {

        override val alertReport: RuleAlertReport.Single<*>?
            get() = null

        val violatedAssertCond: TACExpr
            get() = if (violatedAssert.cmd is TACCmd.Simple.AssertCmd) {
                TACExprFactTypeCheckedOnlyPrimitives.LNot(violatedAssert.cmd.o.asSym())
            } else if (violatedAssert.cmd is TACCmd.Simple.AnnotationCmd && violatedAssert.cmd.annot.v is AssertSnippet<*>) {
                violatedAssert.cmd.annot.v.assertCond.asSym()
            } else {
                error("unexpected CallTrace's violation-command: ${violatedAssert.cmd}")
            }
    }

    class Failure(override val callHierarchyRoot: CVLRootInstance, val exception: CallTraceException, printer: CallTracePrettyPrinter?) : CallTrace() {
        init {
            val instance = CallInstance.ErrorInstance.EarlyExit()
            callHierarchyRoot.addChild(instance)
            printer?.append(instance)
        }

        override val alertReport: RuleAlertReport.Error
            get() = RuleAlertReport.Error(exception.msg, exception)
    }

    data class DisabledByConfig(override val callHierarchyRoot: CVLRootInstance, val conf: ConfigType<*>) : CallTrace() {
        override val alertReport: RuleAlertReport.Warning
            get() = RuleAlertReport.Warning(
                "CallTrace generation was disabled through the command-line (flag: ${conf.name})"
            )
    }

    companion object {
        /**
         * Generates the call trace for [rule] by traversing the control flow graph of the program [program],
         * in topological order. Only blocks that were chosen by the counter-example [model] are visited.
         * The traversal records all the call instances and method summaries that are encountered using a stack,
         * as well as passing of parameters, return values, and return status ([CallEndStatus]).
         * The traversal ends when the first violated assert command is reached.
         */
        operator fun invoke(
            rule: IRule,
            model: CounterexampleModel,
            program: CoreTACProgram,
            formatter: CallTraceValueFormatter,
            scene: ISceneIdentifiers,
            ruleCallString: String,
        ) = CallTraceGenerator(
            rule.declarationId,
            model,
            program,
            formatter,
            scene,
            ruleCallString
        ).safeGenerate()
    }
}

private fun formatCallee(callee: MethodRef, scene: ISceneIdentifiers): String? {
    val (contract, method) = callee.getContractAndMethod(scene) ?: return null

    val caller = if (contract is IClonedContract) {
        val parentContract = scene.getContractOrNull(contract.sourceContractId) ?: return null
        "${parentContract.name}[${contract.createdContractInstance}]"
    } else {
        contract.name
    }

    val methodUIName = if (method.isFallback) {
        CVLReservedVariables.certoraFallbackDisplayName
    } else {
        method.name
    }
    return "$caller.${methodUIName}"
}

/** Returns a map from the word index to its [TACValue], if such a value exists in [model] */
private fun Iterable<InternalFuncRet>.retValsInModel(model: CounterexampleModel): SortedMap<Int, TACValue> {
    val vals = sortedMapOf<Int, TACValue>()

    for ((s, offset) in this) {
        val retVal = model.valueAsTACValue(s)
        if (retVal != null) {
            vals[offset] = retVal
        } else {
            logger.warn { "Value $s at offset $offset, was not found in the model" }
        }
    }

    return vals
}

// sanitizes the string to form a Rule identifier
fun String.toRuleIdentifier(): String {
    return sanitizeRuleName(this)
}

// only use valid java identifier characters for Rule names
private fun sanitizeRuleName(s: String): String =
    s.replace(" ", "_")
        .replace(":", "_")
        .replace(".", "_")
        .filter {
            Character.isJavaIdentifierPart(it)
        }

class CallTraceException(msg: String, t: Throwable? = null) : CertoraException(CertoraErrorType.CALLTRACE, msg, t)

private fun CVLHookPattern.toHookApplicationHeader(labelId: Int): CallInstance.LabelInstance {
    val patternDescription = when (this) {
        is CVLHookPattern.Create -> "create"

        is CVLHookPattern.StoragePattern.Load -> "load ${value.id} := $slot"

        is CVLHookPattern.StoragePattern.Store -> when (val previousValue = previousValue) {
            null -> "store $slot := ${value.id}"
            else -> "store $slot := ${value.id} (old: ${previousValue.id})"
        }

        is CVLHookPattern.Opcode -> when {
            this is PatternWithValue && params.isNotEmpty() -> {
                val joinedParams = params.joinToString(separator = ", ") { param -> param.id }
                "$name($joinedParams) returns ${value.id}"
            }

            this is PatternWithValue -> "$name returns ${value.id}"

            else -> "$name($params)"
        }
    }

    return CallInstance.LabelInstance("Apply hook $patternDescription", labelId = labelId)
}

private fun Logger.warnAndNull(f: () -> String): Nothing? {
    this.warn(f)
    return null
}

/** ad-hoc config flag for now, switching the `altReprs` json entries off / on */
internal const val altReprsInTreeView = true
