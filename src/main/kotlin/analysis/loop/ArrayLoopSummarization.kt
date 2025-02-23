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

package analysis.loop

import analysis.LogicalEquivalence
import analysis.Loop
import analysis.smtblaster.*
import evm.EVM_ARRAY_ELEM_OFFSET
import evm.powersOf2
import parallel.*
import parallel.Scheduler.complete
import smtlibutils.data.SmtExp
import tac.Tag
import utils.keysMatching
import vc.data.TACExpr
import vc.data.TACKeyword
import vc.data.TACSymbol
import vc.data.asTACSymbol
import vc.data.tacexprutil.TACExprFreeVarsCollector
import vc.data.tacexprutil.subs
import java.math.BigInteger

open class ArrayLoopSummarization(private val z3Processor: IBlaster) : AbstractArraySummaryExtractor() {
    private val bvTermBuilder = SmtExpBitVectorTermBuilder
    private val intTermBuilder = SmtExpIntTermBuilder

    protected open val elementSizes = listOf(1.toBigInteger(), 32.toBigInteger())

    interface AccessSummary {
        val roles: Map<TACSymbol.Var, LoopRole>
        val strideBy: BigInteger
        val assumedSize : BigInteger
    }

    protected open fun plausibleAssignment(l: Loop, v: TACSymbol.Var, r: LoopRole) : Boolean {
        return if(r == LoopRole.LENGTH) {
            !couldBeDataSegmentSize(l, v)
        } else if(r == LoopRole.ELEM_LENGTH) {
            couldBeDataSegmentSize(l, v)
        } else {
            true
        }
    }

    protected open fun plausibleArraySize(l: Loop, sz: BigInteger) : Boolean {
        return true
    }

    protected open fun couldBeDataSegmentSize(l: Loop, cand: TACSymbol.Var) : Boolean {
        return false
    }

    protected open fun plausibleRelationalAssignment(correlatedStartVar: TACSymbol.Var, correlatedEndVar: TACSymbol.Var) : Boolean {
        return getRelationalScale(correlatedStartVar, correlatedEndVar) != null
    }

    open protected fun getRelationalScale(correlatedStartVar: TACSymbol.Var, correlatedEndVar: TACSymbol.Var) : BigInteger? {
        return null
    }

    private fun checkRelationalAssignment(m: Map<TACSymbol.Var, LoopRole>) : Boolean {
        if(m.values.none {
            it.relational
            }) {
            return true
        }
        val correlatedStart = m.keysMatching { _, loopRole ->
            loopRole == LoopRole.CORRELATED_ELEM_START
        }.singleOrNull() ?: return false
        val correlatedEnd = m.keysMatching { _, loopRole ->
            loopRole == LoopRole.CORRELATED_ELEM_END
        }.singleOrNull() ?: return false
        return plausibleRelationalAssignment(correlatedStartVar = correlatedStart, correlatedEndVar = correlatedEnd) &&
                getRelationalScale(correlatedStart, correlatedEnd) != null
    }

    data class AliasingAssumption(
        val readExpr: TACExpr,
        val mustNotAlias: List<TACExpr>
    )

    data class ReadEvery(
            override val roles: Map<TACSymbol.Var, LoopRole>,
            override val strideBy: BigInteger,
            override val assumedSize: BigInteger,
            val read: LoopSummarization.MemoryRead,
            val aliasingAssumptions: AliasingAssumption,
            val baseMap: TACSymbol.Var
    ) : AccessSummary

    data class WriteEvery(
            override val roles: Map<TACSymbol.Var, LoopRole>,
            override val strideBy: BigInteger,
            override val assumedSize: BigInteger,
            val write: LoopSummarization.MemoryMutation.MemoryWrite
    ) : AccessSummary

    fun isArrayReadStride(
            summ: LoopSummarization.LoopIterationSummary
    ) : Parallel<List<ReadEvery>> {
        if(summ.exitCondition.hasSelect()) {
            return complete(listOf())
        }
        val indexedReads = summ.memoryReads.values.withIndex()

        val closedForm = interpolateLoop(summ) ?: return complete(listOf())
        return indexedReads.flatMap outer@{ (ind, read) ->
            // first check whether we have must-not aliasing
            val aliasingAssumption = AliasingAssumption(
                    readExpr = read.index,
                    mustNotAlias = indexedReads.mapNotNull {
                        if(it.index == ind) {
                            null
                        } else {
                            it.value.index
                        }
                    }
            )
            if(summ.reachingWrites[LoopSummarization.getWriteTarget(read.base)]?.isNotEmpty() == true) {
                return@outer listOf<Parallel<ReadEvery?>>()
            }
            val short = isStringCopyStride(
                    read = read,
                    closedForm = closedForm,
                    summ = summ
            ) {
                ReadEvery(
                        read = read,
                        aliasingAssumptions = aliasingAssumption,
                        assumedSize = BigInteger.ONE,
                        strideBy = 32.toBigInteger(),
                        roles = it,
                        baseMap = read.base
                )
            }
            if(short != null) {
                return@outer listOf(complete(short))
            }
            if(read.index.hasSelect()) {
                return@outer listOf<Parallel<ReadEvery>>()
            }
            elementSizes.mapNotNull innerMap@{ elementSize ->
                if(!plausibleArraySize(summ.loop, elementSize)) { return@innerMap null }
                checkArrayStriding(elementSize, closedForm, read).maybeBind { strideBy ->
                    checkBoundsCondition(closedForm, summ, read, elementSize).maybeMap {
                        ReadEvery(
                                read = read,
                                aliasingAssumptions = aliasingAssumption,
                                assumedSize = elementSize,
                                strideBy = strideBy,
                                roles = it,
                                baseMap = read.base
                        )
                    }
                }
            }
        }.pcompute().map { results ->
            results.mapNotNull { it }
        }
    }

    private fun <T> isStringCopyStride(
            read: LoopSummarization.MemoryIndexEvent,
            closedForm: Map<TACSymbol.Var, Interpolation>,
            summ: LoopSummarization.LoopIterationSummary,
            f: (Map<TACSymbol.Var, LoopRole>) -> T
    ) : T? {
        return (read.index as? TACExpr.Vec.Add)?.takeIf {
            it.ls.size == 2 && it.operandsAreSyms() && it.o1AsTACSymbol() is TACSymbol.Var && it.o2AsTACSymbol() is TACSymbol.Var
        }?.let short@{
            val o1 = it.o1AsTACSymbol() as TACSymbol.Var
            val o2 = it.o2AsTACSymbol() as TACSymbol.Var
            val basePointerNoMut = closedForm[o1]?.let { it == Interpolation.Identity } ?: false
            val o2Stride32 = closedForm[o2]?.let { it is Interpolation.Linear && it.n == 0x20.toBigInteger() } ?: false
            if(summ.exitCondition !is TACExpr.UnaryExp.LNot ||
                    summ.exitCondition.o !is TACExpr.BinRel.Lt ||
                    !summ.exitCondition.o.operandsAreSyms() ||
                    summ.exitCondition.o.o1 !is TACExpr.Sym.Var ||
                    summ.exitCondition.o.o2 !is TACExpr.Sym.Var) {
                return@short null
            }
            val loopInd = summ.exitCondition.o.o1.s
            val upperBound = summ.exitCondition.o.o2.s
            val exitCondIsLenComparison = loopInd == o2 && (closedForm[upperBound]?.let {
                it == Interpolation.Identity
            } ?: false)
            if(basePointerNoMut && o2Stride32 && exitCondIsLenComparison &&
                    plausibleArraySize(summ.loop, BigInteger.ONE) &&
                    plausibleAssignment(summ.loop, o1, LoopRole.ELEM_START) &&
                    plausibleAssignment(summ.loop, o2, LoopRole.ZERO) &&
                    plausibleAssignment(summ.loop, upperBound, LoopRole.LENGTH)
            ) {
                return f(mapOf(
                                o1 to LoopRole.ELEM_START,
                                o2 to LoopRole.ZERO,
                                upperBound to LoopRole.LENGTH
                        )
                )
            } else {
                null
            }
        }
    }

    fun isArrayWriteStride(
            summ: LoopSummarization.LoopIterationSummary
    ) : Parallel<List<WriteEvery>> {
        if(summ.exitCondition.hasSelect()) {
            return complete(listOf())
        }
        val indexedWrites = summ.getAllWrites().withIndex()
        val closedForm = interpolateLoop(summ) ?: return complete(listOf())
        return indexedWrites.flatMap outer@{ (ind, write) ->
                if(write !is LoopSummarization.MemoryMutation.MemoryWrite) {
                    listOf()
                } else if(!indexedWrites.all { (k, w_) ->
                            if(k == ind) {
                                true
                            } else {
                                mustNeverOverlap(summ, closedForm, w_)
                            }
                        }) {
                    listOf()
                } else if(write.index.hasSelect()) {
                    listOf()
                } else {
                    val shortCircuit = isStringCopyStride(write, closedForm, summ) {
                        WriteEvery(
                                strideBy = 32.toBigInteger(),
                                assumedSize = BigInteger.ONE,
                                write = write,
                                roles = it
                        )
                    }
                    if(shortCircuit != null) {
                        return@outer listOf(complete(shortCircuit))
                    }
                    elementSizes.mapNotNull innerMap@{ elementSize ->
                        if (!plausibleArraySize(summ.loop, elementSize)) {
                            return@innerMap null
                        } else {
                            checkArrayStriding(elementSize, closedForm, write).maybeBind { strideBy ->
                                checkBoundsCondition(closedForm, summ, write, elementSize).maybeMap {
                                    WriteEvery(it, strideBy, elementSize, write)
                                }
                            }
                        }
                    }
                }
        }.pcompute().map { results ->
            results.mapNotNull { it }
        }
    }

    private fun mustNeverOverlap(
            summ: LoopSummarization.LoopIterationSummary,
            closedForm: Map<TACSymbol.Var, Interpolation>,
            otherWrite: LoopSummarization.MemoryMutation
    ): Boolean =
        mustBeFreePointer(summ, otherWrite) && closedForm[TACKeyword.MEM64.toVar()]?.let {
            it == Interpolation.MonotoneTransformation || (it is Interpolation.Linear && it.n >= BigInteger.ZERO)
        } == true

    private fun mustBeFreePointer(
        summ: LoopSummarization.LoopIterationSummary,
        otherWrite: LoopSummarization.MemoryMutation,
    ): Boolean =
        when (otherWrite) {
            is LoopSummarization.MemoryMutation.NestedLoop -> {
                otherWrite.writes.all {
                    mustBeFreePointer(summ, it)
                }
            }
            is LoopSummarization.MemoryMutation.MemoryWrite -> {
                LoopSummarization.isMonotoneTransformerFor(otherWrite.index) {
                    it == TACKeyword.MEM64.toVar()
                }
            }
            is LoopSummarization.MemoryMutation.MemoryCopy -> {
                LoopSummarization.isMonotoneTransformerFor(otherWrite.index) {
                    it == TACKeyword.MEM64.toVar()
                }
            }
            is LoopSummarization.MemoryMutation.MemoryMutationOver -> {
                otherWrite.v.any {
                    LoopSummarization.isMonotoneTransformerFor(it) {
                        it == TACKeyword.MEM64.toVar()
                    }
                }
            }
        }

    protected open fun isConstantSizeArray() : BigInteger? = null

    protected open fun elementStartOffset(): BigInteger = EVM_ARRAY_ELEM_OFFSET

    private fun checkBoundsCondition(
        closedForm: Map<TACSymbol.Var, Interpolation>,
        summ: LoopSummarization.LoopIterationSummary,
        accessEvent: LoopSummarization.MemoryIndexEvent,
        elementSize: BigInteger
    ): Parallel<Map<TACSymbol.Var, LoopRole>?>  {
        val indexExpr = accessEvent.index
        val s = TACExprFreeVarsCollector.getFreeVars(indexExpr).toList()
        val offset = elementStartOffset()

        if(s.any {
                    it !in closedForm
        }) {
            return complete(null)
        }

        val blaster = SmtExpIntBlaster()
        val constantSize = isConstantSizeArray()
        val remainingVars = (TACExprFreeVarsCollector.getFreeVars(summ.exitCondition) - s).toList()
        val work = crossProduct(summ.loop, elementSize, 0, s, mapOf()) {
            val smtCommands = SmtExpScriptBuilder(intTermBuilder)
            if(constantSize != null) {
                smtCommands.assert {
                    eq(
                            toIdent(LoopRole.LENGTH.name),
                            const(constantSize)
                    )
                }
            }
            Companion.addAxioms(smtCommands, elementSize, elemStartOffset = offset)
            for((k, v) in it) {
                if(v == LoopRole.CONSTANT) {
                    smtCommands.define(k.namePrefix) {
                        const(isConstant(k)!!)
                    }
                } else {
                    smtCommands.define(k.namePrefix) { toIdent(v.name) }
                }
            }
            blaster.blastExpr(accessEvent.index) { v ->
                check(v in it)
                v.namePrefix
            }?.let { cmd ->
                smtCommands.assert {
                    lnot(
                            eq(
                                    cmd, toIdent(LoopRole.ELEM_START.name)
                            )
                    )
                }
                smtCommands.checkSat()
                Scheduler.rpc {
                    if (z3Processor.blastSmt(smtCommands.cmdList)) {
                        it
                    } else {
                        null
                    }
                }
            } ?: complete(null as Map<TACSymbol.Var, LoopRole>?)
        }.map {
            it.mapNotNull { it }
        }.bind { assignments ->
            assignments.flatMap { partialAssignment ->
                val newWork = mutableListOf<Parallel<Map<TACSymbol.Var, LoopRole>?>>()
                crossProductNoFork(summ.loop, elementSize = elementSize, i = 0, possibleAssignments = remainingVars, assignment = partialAssignment, output = newWork, mapper = outer@{ assignment ->
                    /**
                     * Assignment is the mapping of pre-loop names (aka, iteration 0) to their expected roles (length, etc)
                     * closedForm is a map from program names to the effects on those program names, as ID, add (or subtract) or constant
                     */
                    if(assignment.any {
                                it.value == LoopRole.ZERO && closedForm[it.key] == Interpolation.Identity
                            }) {
                        return@outer complete(null)
                    }
                    val lastIter = makeSymbol("finalIter")
                    val nondetFreeVars = mutableListOf(lastIter.namePrefix)

                    val monotoneFunctions = mutableMapOf<TACSymbol.Var, Pair<String, TACExpr>>()

                    val initRoleValuation: (TACSymbol.Var) -> TACExpr.Sym = { outer ->
                        val role = assignment[outer]!!
                        if(role == LoopRole.CONSTANT) {
                            isConstant(outer)?.asTACSymbol()?.asSym()!!
                        } else {
                            val nm = role.name
                            TACSymbol.Var(nm, tag = Tag.Bit256).asSym()
                        }
                    }

                    val exitInstantiation: (TACSymbol.Var) -> TACExpr = {
                        instantiateExpressionAt(
                                it,
                                loopIteration = lastIter.asSym(),
                                interp = closedForm[it]!!,
                                functionSymbols = monotoneFunctions,
                                start = initRoleValuation(it)
                        )
                    }

                    val preExitInstantiation : (TACSymbol.Var) -> TACExpr = {
                        instantiateExpressionAt(
                                it,
                                loopIteration = TACExpr.BinOp.Sub(lastIter.asSym(), TACSymbol.lift(1).asSym()),
                                interp = closedForm[it]!!,
                                functionSymbols = monotoneFunctions,
                                start = initRoleValuation(it)
                        )
                    }

                    val exitCondition = instantiateExpr(summ.exitCondition, exitInstantiation)
                    val postExitWriteIndex = instantiateExpr(indexExpr, if(summ.isDoLoop) {
                        { it ->
                            instantiateExpressionAt(it,
                                    loopIteration = TACExpr.Vec.Add(listOf(
                                            lastIter.asSym(), TACSymbol.lift(1).asSym()
                                    )),
                                    functionSymbols = monotoneFunctions,
                                    start = initRoleValuation(it),
                                    interp = closedForm[it]!!
                            )
                        }
                    } else {
                        exitInstantiation
                    })

                    val preExitCondition = instantiateExpr(summ.exitCondition, preExitInstantiation)
                    val preExitWrite = instantiateExpr(indexExpr, if(summ.isDoLoop) {
                        exitInstantiation
                    } else {
                        preExitInstantiation
                    })

                    val smtCommands = SmtExpScriptBuilder(intTermBuilder)
                    val scaleSize = assignment.entries.find {
                        it.value == LoopRole.CORRELATED_ELEM_START
                    }?.let { startVar ->
                        val endVar = assignment.entries.find {
                            it.value == LoopRole.CORRELATED_ELEM_END
                        }!!
                        getRelationalScale(startVar.key, endVar.key)
                    }
                    if(constantSize != null) {
                        smtCommands.assert {
                            eq(
                                    toIdent(LoopRole.LENGTH.name),
                                    const(constantSize)
                            )
                        }
                    }
                    Companion.addAxioms(smtCommands, elementSize, scaleSize, elemStartOffset = offset)
                    for(d in nondetFreeVars) {
                        smtCommands.declare(d)
                    }
                    smtCommands.assert { ge(toIdent(lastIter.namePrefix), const(0)) }

                    axiomatizeFunctions(smtCommands, monotoneFunctions.values){
                        blaster.blastExpr(it) { it.toSMTRep() }
                    }
                    // now assert that the exit condition is true
                    /*
                       The exit condition is in terms of the pre-loop names, so remap them
                       to the L1... versions computed above in lastIteration, aka their value
                       after finalIter iterations
                    */
                    val pc = blaster.blastExpr(exitCondition) {
                        it.toSMTRep()
                    } ?: return@outer complete(null)

                    /*
                        Let's make sure we can some loop termination (this is a sanity check)
                     */
                    smtCommands.fork().let { ex ->
                        ex.assert {
                            lnot(eq(pc, const(0)))
                        }
                        ex.checkSat()
                        // if (= pc 0) is unsat, then from the original conditions we can never exit the loop. NOPE
                        if(z3Processor.blastSmt(ex.cmdList)) {
                            return@outer complete(null)
                        }
                    }

                    /*
                      Assert the program condition must be true (aka not 0)
                     */
                    smtCommands.assert {
                        lnot(eq(pc, const(0)))
                    }

                    /* now, get the valuation of the write index on this final iteration
                       Again, this write is in terms of pre-loops, so compute what the value would
                       be in the n+1th iteration, by mapping pre names to L1... which are defined
                       above
                     */
                    val writeIdx = blaster.blastExpr(postExitWriteIndex) {
                        it.toSMTRep()
                    } ?: return@outer complete(null)
                    val pastEndCommands = smtCommands.fork()
                    pastEndCommands.assert {
                        lt(writeIdx, toIdent(LoopRole.END.name))
                    }
                    pastEndCommands.assert {
                        ge(writeIdx, toIdent(LoopRole.ZERO.name))

                    }
                    pastEndCommands.checkSat()

                    // immediately *before* the last iteration, are we before the end?
                    val preEndCommands = smtCommands.fork()
                    /*
                      For value in the nth iteration, compute the n-1th iteration form, aka the value
                      before the nth iteration completed
                     */
                    /*
                     * Compute the program condition that must have been true for the n-1th iteration to execute
                     */
                    val prevPc = blaster.blastExpr(preExitCondition) {
                        it.toSMTRep()
                    } ?: return@outer complete(null)

                    val preWriteIdx = blaster.blastExpr(preExitWrite) {
                        it.toSMTRep()
                    } ?: return@outer complete(null)
                    /*
                      Assert that the final write must have been within bounds
                     */
                    preEndCommands.assert {
                        ge(preWriteIdx, toIdent(LoopRole.END.name))
                    }
                    preEndCommands.assert {
                        ge(preWriteIdx, const(0))
                    }
                    /*
                      assert that we must have taken this branch
                    */
                    preEndCommands.assert {
                        eq(prevPc, const(0))
                    }
                    preEndCommands.checkSat()
                    val pastEndIO = rpc {
                        z3Processor.blastSmt(pastEndCommands.cmdList)
                    }
                    val preEndIO = rpc {
                        z3Processor.blastSmt(preEndCommands.cmdList)
                    }
                    preEndIO.parallelBind(pastEndIO) { a, b ->
                        if(a && b) {
                            complete(assignment as Map<TACSymbol.Var, LoopRole>?)
                        } else {
                            complete(null as Map<TACSymbol.Var, LoopRole>?)
                        }
                    }
                })
                newWork
            }.pcompute().map {
                it.mapNotNull { it }
            }.map {
                it.singleOrNull()
            }
        }
        return work
    }

    private fun <T> crossProduct(
        l: Loop,
        elementSize: BigInteger,
        i: Int,
        possibleAssignments: List<TACSymbol.Var>,
        assignment: Map<TACSymbol.Var, LoopRole>,
        mapper: (Map<TACSymbol.Var, LoopRole>) -> Parallel<T?>
    ) : Parallel<List<T?>> {
        if(i >= 1) {
            val output = mutableListOf<Parallel<T?>>()
            crossProductNoFork(l, elementSize, i, possibleAssignments, assignment, output, mapper)
            return output.pcompute()
        } else {
            return if (i == possibleAssignments.size) {
                if(!checkRelationalAssignment(assignment)) {
                    return complete(listOf())
                } else {
                    mapper(assignment).bind {
                        complete(listOf(it))
                    }
                }
            } else {
                val output = mutableListOf<Parallel<List<T?>>>()
                for (x in LoopRole.values()) {
                    if (!checkAssignment(x, assignment, l, possibleAssignments, i, elementSize)) {
                        continue
                    }
                    output.add(Scheduler.fork {
                        crossProduct(l, elementSize, i + 1, possibleAssignments, assignment + (possibleAssignments[i] to x), mapper)
                    })
                }
                output.pcompute().bind { it ->
                    complete(it.flatten())
                }
            }
        }
    }

    private fun <T> crossProductNoFork(
            l: Loop,
            elementSize: BigInteger,
            i: Int,
            possibleAssignments: List<TACSymbol.Var>,
            assignment: Map<TACSymbol.Var, LoopRole>,
            output: MutableList<Parallel<T?>>,
            mapper: (Map<TACSymbol.Var, LoopRole>) -> Parallel<T?>
    ) {
        if(i == possibleAssignments.size) {
            if(!checkRelationalAssignment(assignment)) {
                return
            }
            output.add(mapper(assignment))
        } else {
            for(x in LoopRole.values()) {
                if (!checkAssignment(x, assignment, l, possibleAssignments, i, elementSize)) {
                    continue
                }
                crossProductNoFork(l, elementSize, i + 1, possibleAssignments, assignment + (possibleAssignments[i] to x), output, mapper)
            }
        }
    }

    private fun checkAssignment(x: LoopRole, assignment: Map<TACSymbol.Var, LoopRole>, l: Loop, possibleAssignments: List<TACSymbol.Var>, i: Int, elementSize: BigInteger): Boolean {
        if (x != LoopRole.CONSTANT && x in assignment.values) {
            return false
        }
        if(x == LoopRole.ELEM_LENGTH && (elementSize == BigInteger.ONE || !couldBeDataSegmentSize(l, possibleAssignments[i]))) {
            return false
        }
        if(x == LoopRole.CONSTANT && isConstant(possibleAssignments[i]).let {
                /*
                   zero is handld with a special loop role for annoying reasons
                   fixme(jtoman): it probably shouldn't be
                 */
                it == null || it == BigInteger.ZERO || it == isConstantSizeArray()
            }) {
            return false
        }
        // checked later
        if(x.relational) {
            return true
        }
        return plausibleAssignment(l, possibleAssignments[i], x)
    }

    @Suppress("NAME_SHADOWING") // prevNext, nextPrev
    private fun checkArrayStriding(
        elementSize: BigInteger,
        closedForm: Map<TACSymbol.Var, Interpolation>,
        accessEvent: LoopSummarization.MemoryIndexEvent
    ): Parallel<BigInteger?> {
        val nextWrite = makeSymbol("next")
        val initMap = mutableMapOf<TACSymbol.Var, TACExpr>()
        val initValuation: (TACSymbol.Var) -> TACExpr = { tgt ->
            initMap.computeIfAbsent(tgt) { _ ->
                TACExpr.Sym(
                    TACSymbol.Var(
                            tgt.namePrefix + "_Init",
                            tag = tgt.tag
                    )
                )
            }
        }
        if(TACExprFreeVarsCollector.getFreeVars(accessEvent.index).any {
            it !in closedForm
        }) {
            return complete(null)
        }
        val funSymbols = mutableMapOf<TACSymbol.Var, Pair<String, TACExpr>>()
        val prevIter = instantiateExpr(accessEvent.index) {
            instantiateExpressionAt(
                    it,
                    start = initValuation(it),
                    functionSymbols = funSymbols,
                    interp = closedForm[it] ?: error("Could not find $it in $closedForm"),
                    loopIteration = TACExpr.BinOp.Sub(
                            TACExpr.Sym(nextWrite),
                            TACExpr.Sym(TACSymbol.lift(1))
                    )
            )
        }
        val nextIter = instantiateExpr(accessEvent.index) {
            instantiateExpressionAt(
                    it,
                    start = initValuation(it),
                    functionSymbols = funSymbols,
                    interp = closedForm[it]!!,
                    loopIteration =
                    TACExpr.Sym(nextWrite)
            )
        }
        val axioms = SmtExpScriptBuilder(bvTermBuilder).let {
            this.axiomatizeFunctions(it, funSymbols.values) {
                ExpressionTranslator(bvTermBuilder, List<SmtExp>::toTypedArray).blastExpr(it) { it.toSMTRep() }
            }
            it.cmdList
        }
        val eSzExpr = TACExpr.Sym(TACSymbol.lift(elementSize))
        val prevDiffNext = TACExpr.BinOp.Sub(
                prevIter,
                nextIter
        )
        val nextDiffPrev = TACExpr.BinOp.Sub(
                nextIter, prevIter
        )

        return Scheduler.rpc {
            LogicalEquivalence.equiv(axioms, prevDiffNext, eSzExpr, z3Processor)
        } with Scheduler.rpc {
            LogicalEquivalence.equiv(axioms, nextDiffPrev, eSzExpr, z3Processor)
        } andThen { prevNext, nextPrev ->
            if(prevNext) {
                `return`<BigInteger?>(elementSize.negate())
            } else if(nextPrev) {
                `return`<BigInteger?>(elementSize)
            } else if(elementSize == BigInteger.ONE) {
                rpc {
                    LogicalEquivalence.equiv(axioms, prevDiffNext, TACSymbol.lift(32).asSym(), z3Processor)
                } with rpc {
                    LogicalEquivalence.equiv(axioms, nextDiffPrev, TACSymbol.lift(32).asSym(), z3Processor)
                } andThenReturn { prevNext, nextPrev ->
                    if(prevNext) {
                        (-32).toBigInteger()
                    } else if(nextPrev) {
                        32.toBigInteger()
                    } else {
                        null
                    }
                }
            } else {
                `return`(null)
            }
        }
    }

    fun isCopyLoop(
            readEvery: ReadEvery,
            writeEvery: WriteEvery
    ) : Boolean {
        for((k, v) in readEvery.roles) {
            if(writeEvery.roles[k]?.let {
                        it == v
                    } == false) {
                return false
            }
        }
        if(readEvery.strideBy != writeEvery.strideBy) {
            return false
        }
        val x = writeEvery.write
        val selectOperation = when(val d = x.value) {
            is TACExpr.BinOp.BWAnd -> {
                val (select,mask) = if(d.o1 is TACExpr.Select) {
                    d.o1 to d.o2
                } else if(d.o2 is TACExpr.Select) {
                    d.o2 to d.o1
                } else {
                    return false
                }
                val maskConst = mask.evalAsConst() ?: return false
                if((maskConst + BigInteger.ONE) !in powersOf2) {
                    return false
                }
                select
            }
            is TACExpr.BinOp.SignExtend -> {
                if(d.o2 !is TACExpr.Select) {
                    return false
                }
                d.o2
            }
            is TACExpr.Select -> d
            else -> return false
        }
        if(selectOperation.base !is TACExpr.Sym) {
            return false
        }
        if(readEvery.read.base != selectOperation.base.s || readEvery.read.index != selectOperation.loc) {
            return false
        }
        if(readEvery.aliasingAssumptions.mustNotAlias.isNotEmpty()) {
            return false
        }
        return true
    }

    private fun makeSymbol(v: String) = TACSymbol.Var(namePrefix = v, tag = Tag.Bit256)

    private fun TACExpr.hasSelect() = subs.any { it is TACExpr.Select }

}
