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

package analysis.alloc

import analysis.*
import analysis.dataflow.LiveVariableAnalysis
import analysis.numeric.*
import analysis.pta.LoopCopyAnalysis
import analysis.worklist.IWorklistScheduler
import analysis.worklist.MonadicStatefulParallelWorklistIteration
import analysis.worklist.NaturalBlockScheduler
import analysis.worklist.ParallelStepResult
import com.certora.collect.*
import log.Logger
import log.LoggerTypes
import parallel.ParallelPool
import tac.NBId
import utils.*
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACKeyword
import vc.data.TACSymbol
import java.math.BigInteger

private typealias Continuation = (MutableCollection<NBId>, MutableCollection<Result>) -> Unit

private val logger = Logger(LoggerTypes.ALLOC)

private sealed class Result {
    /**
     * The read at [read] might be a scratch pointer: it fell out of scope at some point without being definitively
     * classified as scratch or not. If there is no other classification information, then [read] should be scratch
     */
    data class MayScratch(val read: CmdPointer) : Result()

    /**
     * The read at [read] *must* be a scratch pointer read
     */
    data class MustScratch(val read: CmdPointer) : Result()

    /**
     * The read at [read] definitely reaches the free pointer write at [write]. Each read must be
     * paired with at most one write location, and a paired read cannot be classified as scratch.
     */
    data class MustReachWrite(val read: CmdPointer, val write: CmdPointer) : Result()

    /**
     * The read at [read] must either be a bytes array allocation OR a scratch. In general we don't allow reads
     * from free pointer unless:
     * a) They are a scratch pointer
     * b) the are a packed bytes allocation
     *
     * When we see a read from a free pointer, we record this fact, and resolve it later.
     */
    data class MustScratchOrByte(val read: CmdPointer) : Result()

    /**
     * We experienced an allocation failure at [loc]
     */
    data class Fail(val loc: CmdPointer) : Result()

    /**
     * The free pointer read at [readLoc] must have the same classification as that in [equivTo]. If [readLoc]
     * has already been classified, the classifications must match, otherwise the [equivTo] classification
     * is propagated to [readLoc]. This propagation is unidirectional (if [readLoc] is classified and [equivTo] is not,
     * then this fact will have no effect).
     */
    data class EquivalentClass(val readLoc: CmdPointer, val equivTo: CmdPointer) : Result()
}

private sealed class PointerVal {
    abstract val must: Boolean
    abstract val reach: TreapSet<CmdPointer>

    abstract fun withWeak() : PointerVal
}

private data class MustScratch(
        override val must: Boolean,
        override val reach: TreapSet<CmdPointer>
) : PointerVal() {
    override fun withWeak(): MustScratch {
        if(!this.must) {
            return this
        }
        return this.copy(must = false)
    }
}

private data class LivePointer(
        val readSite: CmdPointer,
        val readSiteWriteId: Int,
        override val must: Boolean
) : PointerVal() {
    override val reach: TreapSet<CmdPointer>
        get() = treapSetOf(readSite)

    override fun withWeak(): LivePointer {
        if(!this.must) {
            return this
        }
        return this.copy(must = false)
    }
}

private data class FPState(
        val offsets: TreapMap<TACSymbol.Var, IntValue>,
        val readStat: TreapMap<TACSymbol.Var, PointerVal>
)

object ScratchPointerAnalysis {
    data class AnalysisResult(
        val reachesWrite: TreapMap<CmdPointer, CmdPointer>,
        val scratchReads: TreapSet<CmdPointer>,
        val mustByte: TreapSet<CmdPointer>,
        val failurePoints: TreapSet<CmdPointer>
    )

    private class ScratchAnalysisWorker(
        private val reachingWriteId: TreapMap<CmdPointer, Int>,
        private val lva: LiveVariableAnalysis,
        private val graph: TACCommandGraph,
        private val offsets: TreapMap<CmdPointer, BigInteger>,
        private val knownScratch: TreapSet<CmdPointer>,
        private val fakeAllocWriteLoc: TreapMap<CmdPointer, AllocationAnalysis.FakeAllocSort>,
        private val initialFreePointerVal: BigInteger,
    ) : MonadicStatefulParallelWorklistIteration<NBId,Continuation, Result, AnalysisResult>(
      inheritPool = (Thread.currentThread() as? ParallelPool.ParallelPoolWorkerThread)?.parallelPool
    ) {
        override val scheduler: IWorklistScheduler<NBId> = NaturalBlockScheduler(graph)

        override fun commit(c: Continuation, nxt: MutableCollection<NBId>, res: MutableCollection<Result>) {
            c.invoke(nxt, res)
        }

        override fun reduce(results: List<Result>): AnalysisResult {
            val reachingWrites = treapMapBuilderOf<CmdPointer, CmdPointer>()
            val scratchReads = treapSetBuilderOf<CmdPointer>()
            val mayByte = treapSetBuilderOf<CmdPointer>()
            val mustByte = treapSetBuilderOf<CmdPointer>()
            val mayScratch = treapSetBuilderOf<CmdPointer>()

            val equiv = treapMapBuilderOf<CmdPointer, CmdPointer>()

            val failSites = treapSetBuilderOf<CmdPointer>()

            /**
             * This for loop computes the classification for each read site.
             *
             * A read site that is [Result.MayScratch] that is unclassified by the end of the for loop
             * is assumed to scratch.
             *
             * A read site that [MustScratch] is definitively a scratch pointer. If the pointer is also
             * classified as reaching a write, the analysis records an error.
             *
             * A read site that [analysis.alloc.Result.MustReachWrite] cannot scratch, and is assumed to be an allocation.
             * If the read site [analysis.alloc.Result.MustScratchOrByte] (recorded in `mayByte`),
             * then the read site must be a bytes array allocation (recorded in `mustByte).
             *
             * The fact that a read [analysis.alloc.Result.MustScratchOrByte] that is also known to [MustScratch]
             * is ignored: we already know it must scratch.
             *
             * A read considered [analysis.alloc.Result.EquivalentClass] to another read must have the same classification.
             * Otherwise, if no classification is yielded at the end of the loop, the classification of
             * [analysis.alloc.Result.EquivalentClass.equivTo] is propagated to [analysis.alloc.Result.EquivalentClass.readLoc]
             */

            outer@for(r in results) {
                when(r) {
                    /*
                       If we have already definitively results this read site, ignore this fact. Otherwise, record
                       that we may need to "default" to classifying the read to a scratch.
                     */
                    is Result.MayScratch -> if(r.read !in reachingWrites && r.read !in scratchReads) {
                        mayScratch.add(r.read)
                    }
                    is Result.MustScratch -> {
                        /*
                         Cannot be both
                         */
                        if(r.read in reachingWrites) {
                            logger.warn {
                                "Found that read ${r.read} which must scratch reaches a write at ${reachingWrites[r.read]}, scratch violation"
                            }
                            // Then we have a scratch pointer that on some path reached a FP write. Nope
                            failSites.add(r.read)
                            continue@outer
                        }
                        scratchReads.add(r.read)
                        /*
                          mayByte only records that a read that is POTENTIALLY classified as an allocation must be
                          a bytes array allocation. We just determined this read is NOT an allocation, so delete this
                          fact.
                         */
                        mayByte.remove(r.read)
                        /*
                          No "may" about it
                         */
                        mayScratch.remove(r.read)
                    }
                    is Result.MustReachWrite -> {
                        /*
                          Again, we can't have a duplicate classification
                         */
                        if(r.read in scratchReads) {
                            logger.warn {
                                "Have that read ${r.read} which reaches write at ${r.write} must scratch"
                            }
                            failSites.add(r.read)
                            continue@outer
                        }
                        /*
                          mayScratch only records those reads that may be scratch reads absent other information. We now
                          have information, so kill this fact.
                         */
                        mayScratch.remove(r.read)
                        val curr = reachingWrites[r.read]
                        if(curr == null) {
                            reachingWrites[r.read] = r.write
                        } else if(curr != r.write) {
                            /*
                             Cannot have inconsistent FP write sites
                             */
                            logger.warn {
                                "Have that we reach different writes from ${r.read}, ${r.write} vs ${reachingWrites.get(r.read)}"
                            }
                            failSites.add(r.read)
                            // inconsistent post domination, so nooope
                            continue@outer
                        }
                        /*
                          mayByte records that a read, IF classified as an allocaiton, MUST be a bytes array.
                          We now know it must indeed be an allocation, so record that is MUST be a bytes array.
                         */
                        if(r.read in mayByte) {
                            mayByte.remove(r.read)
                            mustByte.add(r.write)
                        }
                    }
                    is Result.MustScratchOrByte -> {
                        /*
                          If we already know the read must scratch, this fact is redundant
                         */
                        if(r.read in scratchReads) {
                            continue@outer
                        } else if(r.read in reachingWrites) {
                            /*
                               Then the precondition for our fact must hold (i.e., it is an allocation) ergo, record
                               it must be a bytes array
                             */
                            mustByte.add(reachingWrites[r.read]!!)
                        } else {
                            /*
                              Defer resolution until later.
                             */
                            mayByte.add(r.read)
                        }
                    }
                    is Result.Fail -> failSites.add(r.loc)
                    is Result.EquivalentClass -> {
                        /*
                          if equiv for readLoc is non-null and NOT equal to the equivalence site we already have,
                          fail (we could go full union-find but woof)
                         */
                        if(equiv[r.readLoc]?.equals(r.equivTo) == false) {
                            logger.warn {
                                "Already have an equivalence relationship for $r, namely ${equiv[r.readLoc]}"
                            }
                            failSites.add(r.readLoc)
                            continue@outer
                        }
                        equiv[r.readLoc] = r.equivTo
                    }
                }
            }
            for((r, parent) in equiv) {
                if(parent in reachingWrites) {
                    if(reachingWrites[r]?.equals(reachingWrites[parent]!!) == false) {
                        logger.warn {
                            "Expected $r to have same classification as $parent, but it is already " +
                                    "resolved to a different write site: ${reachingWrites[r]} vs ${reachingWrites[parent]}"
                        }
                        failSites.add(r)
                        continue
                    }
                    if(r in scratchReads) {
                        logger.warn {
                            "Expected $r to have same classification as $parent, but $parent reaches write ${reachingWrites[parent]} " +
                                    "while $r is known to scratch"
                        }
                        failSites.add(r)
                        continue
                    }
                    reachingWrites[r] = reachingWrites[parent]!!
                    mayScratch.remove(r)
                }
                if(parent in mustByte) {
                    mustByte.add(r)
                }
                if(parent in scratchReads) {
                    if(reachingWrites[r] != null) {
                        logger.warn {
                            "Expected $r to have same classification as $parent, but $parent is known to scratch, while $r reaches " +
                                    "write ${reachingWrites[r]}"
                        }
                        failSites.add(r)
                        continue
                    }
                    scratchReads.add(r)
                }
            }
            /*
              Any remaining may scratches that were not provably a must not scratch are now transformed to must scratch
             */
            scratchReads.addAll(mayScratch)
            return AnalysisResult(reachingWrites.build(), scratchReads.build(), mustByte.build(), failSites.build())
        }

        private val state = graph.rootBlocks.map {
            it.id to FPState(
                    treapMapOf(),
                    treapMapOf()
            )
        }.toMap().toMutableMap()
        private val joinCount = mutableMapOf<NBId, Int>()

        override fun process(it: NBId): ParallelStepResult<Continuation, Result, AnalysisResult> {
            logger.trace {
                "Visiting $it"
            }
            val st = state[it]!!

            val results = mutableListOf<Result>()
            val block = graph.elab(it)

            val toRemove = mutableSetOf<TACSymbol.Var>()
            val toCorrupt = mutableSetOf<TACSymbol.Var>()
            var hasLiveInvalid: Boolean

            val stopWithResult by lazy {
                this.result(results)
            }

            fun recordFailureAt(v: CmdPointer): ParallelStepResult<Continuation, Result, AnalysisResult> {
                results.add(Result.Fail(v))
                return stopWithResult
            }

            /*
            A map of variables to pointer states, of type [PointerVal]
             */
            val pointerStateMap = st.readStat.builder()
            var num = st.offsets

            for(l in block.commands) {
                toRemove.clear()
                toCorrupt.clear()
                val live = lva.liveVariablesBefore(l.ptr)
                hasLiveInvalid = false
                for((k, pSt) in pointerStateMap) {
                    if(k !in live) {
                        if(pSt is LivePointer) {
                            results.add(Result.MayScratch(pSt.readSite))
                        }
                        toRemove.add(k)
                    } else if(pSt is MustScratch) {
                        hasLiveInvalid = true
                    } else if(pSt is LivePointer && (pSt.readSiteWriteId != reachingWriteId[l.ptr] || l.ptr in fakeAllocWriteLoc)) {
                        results.add(Result.MustScratch(pSt.readSite))
                        toCorrupt.add(k)
                        hasLiveInvalid = true
                    }
                }
                if(hasLiveInvalid && isFreePointerWrite(l) && l.ptr !in fakeAllocWriteLoc) {
                    logger.warn {
                        "At free pointer write $l, found a live scratch pointers $pointerStateMap"
                    }
                    return recordFailureAt(l.ptr)
                }
                for(p in toCorrupt) {
                    if(p in toRemove) {
                        continue
                    }
                    val x = pointerStateMap[p]
                    check(x != null && x is LivePointer)
                    pointerStateMap[p] = MustScratch(must = x.must, reach = treapSetOf(x.readSite))
                }
                for(v in toRemove) {
                    pointerStateMap.remove(v)
                }

                val numNxt = interpreter.step(l, FPState(num, pointerStateMap.build()))
                if(isFreePointerRead(l)) {
                    val view = l.narrow<TACCmd.Simple.AssigningCmd>()
                    if(hasLiveInvalid || l.ptr in knownScratch) {
                        pointerStateMap[view.cmd.lhs] = MustScratch(must = true, reach = treapSetOf(l.ptr))
                        results.add(Result.MustScratch(l.ptr))
                    } else {
                        pointerStateMap[view.cmd.lhs] = LivePointer(
                                must = true,
                                readSite = l.ptr,
                                readSiteWriteId = reachingWriteId[l.ptr]!!
                        )
                    }
                    num = numNxt
                    continue
                }
                if(isFreePointerWrite(l)) {
                    if(l.ptr !in fakeAllocWriteLoc) {
                        if (l.cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd
                            || ((l.cmd.rhs is TACExpr.Sym.Var && l.cmd.rhs.s !in pointerStateMap)
                                || (l.cmd.rhs is TACExpr.Sym.Const && l.cmd.rhs.s.value != initialFreePointerVal))
                        ) {
                            logger.warn {
                                "At $l, writing an untracked pointer to the free pointer??!?!"
                            }
                            return recordFailureAt(l.ptr)
                        }
                        val hasStrongReach = mutableSetOf<CmdPointer>()
                        val hasWeakReach = mutableSetOf<CmdPointer>()
                        for ((_, v) in pointerStateMap) {
                            check(v is LivePointer) // otherwise we would have hasLiveInvalid
                            if (v.must) {
                                hasStrongReach.add(v.readSite)
                            } else {
                                hasWeakReach.add(v.readSite)
                            }
                        }
                        for (w in hasStrongReach) {
                            results.add(Result.MustReachWrite(read = w, write = l.ptr))
                        }
                        hasWeakReach -= hasStrongReach
                        hasWeakReach.mapTo(results) { Result.MustScratch(read = it) }
                    }
                    /*
                    TODO(jtoman): This is very unsound, because this write could be a fake alloc, in which case we still
                    have some scratch pointers floating around. For the moment, YOLO, but we should introduce a notion
                    of read-only scratch pointers which can persist past allocations, and rw, which cannot.
                     */
                    // stop tracking offsets here
                    if(l.ptr in fakeAllocWriteLoc) {
                        val sort = fakeAllocWriteLoc[l.ptr]!!
                        if(sort == AllocationAnalysis.FakeAllocSort.ECRECOVER) {
                            continue
                        }
                    }
                    num = numNxt - pointerStateMap.keys
                    pointerStateMap.clear()
                    continue
                }
                val usage = FreePointerAnalysis.classifyUse(
                        must = object : AbstractCollection<TACSymbol.Var>() {
                            override val size: Int
                                get() = iterator().asSequence().count()

                            override fun iterator(): Iterator<TACSymbol.Var> {
                                return pointerStateMap.entries.stream().filter {
                                    it.value.must
                                }.map {
                                    it.key
                                }.iterator()
                            }

                            override fun contains(element: TACSymbol.Var): Boolean {
                                return pointerStateMap.get(element)?.must == true
                            }
                        },
                        may = pointerStateMap.keys,
                        num = num,
                        lc = l
                )
                when(usage) {
                    null -> {
                        if(l.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && l.cmd.rhs is TACExpr.BinOp.Sub &&
                            l.cmd.rhs.operandsAreSyms() && listOf(l.cmd.rhs.o1, l.cmd.rhs.o2).all {
                                    it is TACExpr.Sym.Var && (pointerStateMap[it.s] as? LivePointer)?.must == true
                                }
                            ) {
                            val firstRead = ((l.cmd.rhs.o1 as TACExpr.Sym.Var).s.let(pointerStateMap::get) as LivePointer).readSite
                            val secondRead = ((l.cmd.rhs.o2 as TACExpr.Sym.Var).s.let(pointerStateMap::get) as LivePointer).readSite
                            if(firstRead != secondRead) {
                                results.add(Result.EquivalentClass(readLoc = secondRead, equivTo = firstRead))
                            }
                        }
                        killPointer(l, pointerStateMap)
                    }
                    UseSort.MemWrite -> {
                        killPointer(l, pointerStateMap)
                    }
                    UseSort.MemRead -> {
                        val src = l.narrow<TACCmd.Simple.AssigningCmd>().cmd.getFreeVarsOfRhs().mapNotNull {
                            pointerStateMap[it]
                        }
                        src.forEach {
                            // we can only read from pointers that must scratch
                            if(it is LivePointer) {
                                results.add(Result.MustScratchOrByte(it.readSite))
                            }
                        }
                        killPointer(l, pointerStateMap)
                    }
                    UseSort.Escape, UseSort.Unsafe -> {
                        logger.warn {
                            "At $l in state $pointerStateMap and $num, got unsafe use $usage"
                        }
                        return recordFailureAt(l.ptr)
                    }
                    UseSort.Value -> {
                        val src = l.narrow<TACCmd.Simple.AssigningCmd>().cmd.getFreeVarsOfRhs().mapNotNull {
                            pointerStateMap[it]
                        }
                        killPointer(l, pointerStateMap)
                        ptaInvariant(src.isNotEmpty()) {
                            "Said we used a value in $l, but go no references in rhs"
                        }
                        pointerStateMap[l.narrow<TACCmd.Simple.AssigningCmd>().cmd.lhs] = src.foldFirst { a, b ->
                            joinPointerVal(a, b, results)
                        }
                    }
                }
                num = numNxt
            }
            val blockSucc = graph.succ(it).let {
                val last = block.commands.last()
                if(last.cmd is TACCmd.Simple.SummaryCmd && last.cmd.summ is LoopCopyAnalysis.LoopCopySummary) {
                    it - last.cmd.summ.skipTarget
                } else {
                    it
                }
            }.filter {
                it !in graph.cache.revertBlocks
            }
            if(blockSucc.isEmpty()) {
                pointerStateMap.forEach { (_, v) ->
                    for(pendingRead in v.reach) {
                        results.add(Result.MustScratch(pendingRead))
                    }
                }
                return this.result(results)
            }
            return ParallelStepResult.FullResult(
                    res = results,
                    cont = listOf { nxt, res ->
                        for(s in blockSucc) {
                            if(s !in state) {
                                state[s] = FPState(offsets = num, readStat = pointerStateMap.build())
                                joinCount[s] = 0
                                nxt.add(s)
                                continue
                            }
                            val joinCount = joinCount.merge(s, 1, Int::plus)!!
                            val curr = state[s]!!
                            val toQueue = run {
                                val numMergeJob = run {
                                    val m = if(joinCount < 2) {
                                        curr.offsets.join(num, IntValue.Nondet)
                                    } else {
                                        curr.offsets.widen(num, IntValue.Nondet)
                                    }
                                    if(m == curr.offsets) {
                                        null
                                    } else {
                                        m
                                    }
                                }
                                val pointerJob = run {
                                    val currMut = curr.readStat.builder()
                                    val currKeys = curr.readStat.keys.builder()
                                    for((k, v) in pointerStateMap) {
                                        currKeys -= k
                                        if(k !in currMut) {
                                            currMut[k] = v.withWeak()
                                        } else {
                                            currMut[k] = joinPointerVal(v, currMut[k]!!, res)
                                        }
                                    }
                                    for(k in currKeys) {
                                        currMut[k] = currMut[k]!!.withWeak()
                                    }
                                    if(currMut == curr.readStat) {
                                        null
                                    } else {
                                        currMut
                                    }
                                }
                                if(numMergeJob != null || pointerJob != null) {
                                    FPState(numMergeJob ?: curr.offsets, readStat = pointerJob?.build() ?: curr.readStat)
                                } else {
                                    null
                                }
                            }
                            if(toQueue != null) {
                                state[s] = toQueue
                                nxt.add(s)
                            }
                        }
                    }
            )
        }

        private fun killPointer(l: LTACCmd, map: MutableMap<TACSymbol.Var, PointerVal>) {
            if (l.cmd is TACCmd.Simple.AssigningCmd) {
                map -= l.cmd.lhs
            }
        }

        private fun joinPointerVal(a: PointerVal, b: PointerVal, results: MutableCollection<Result>): PointerVal {
            return if (a is MustScratch || b is MustScratch) {
                MustScratch(must = b.must && a.must,
                        reach = if (a.reach === b.reach) {
                            a.reach
                        } else {
                            a.reach + b.reach
                        })
            } else {
                check(a is LivePointer && b is LivePointer)
                if (a.readSite != b.readSite) {
                    results.add(Result.MustScratch(a.readSite))
                    results.add(Result.MustScratch(b.readSite))
                    MustScratch(must = b.must && a.must, reach = treapSetOf(a.readSite, b.readSite))
                } else if (a.must != b.must) {
                    assert(a.readSiteWriteId == b.readSiteWriteId)
                    a.copy(
                            must = a.must && b.must
                    )
                } else {
                    a
                }
            }
        }

        private val interpreter =
                object : SimpleAbstractInterpreter<TreapMap<TACSymbol.Var, IntValue>, FPState>(expressionInterpreter = object : FunctionStateIntervalSemantics<FPState>(
                        object : IValueSemantics<Map<TACSymbol.Var, IntValue>, IntValue, FPState> by SimpleIntervalValueSemantics {
                            override fun evalAdd(v1: IntValue, o1: TACSymbol, v2: IntValue, o2: TACSymbol, toStep: Map<TACSymbol.Var, IntValue>, input: Map<TACSymbol.Var, IntValue>, whole: FPState, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): IntValue {
                                val ret = SimpleIntervalValueSemantics.evalAdd(v1, o1, v2, o2, toStep, input, whole, l)
                                if (ret == IntValue.Nondet) {
                                    val mustPointerArg = listOf(o1, o2).filter {
                                        whole.readStat[it]?.must == true
                                    }
                                    if (mustPointerArg.size == 1) {
                                        val newLb = v1.lb + v2.lb
                                        if (newLb <= MAX_UINT) {
                                            return IntValue.Interval(lb = newLb)
                                        }
                                    }
                                }
                                return ret
                            }

                            override fun evalIte(
                                i: IntValue,
                                iSym: TACSymbol,
                                t: IntValue,
                                tSym: TACSymbol,
                                e: IntValue,
                                eSym: TACSymbol,
                                toStep: Map<TACSymbol.Var, IntValue>,
                                input: Map<TACSymbol.Var, IntValue>,
                                whole: FPState,
                                l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
                            ): IntValue {
                                return SimpleIntervalValueSemantics.evalIte(i, iSym, t, tSym, e, eSym, toStep, input, whole, l)
                            }
                        }
                ) {
                    override fun interp(o1: TACSymbol, toStep: TreapMap<TACSymbol.Var, IntValue>, input: TreapMap<TACSymbol.Var, IntValue>, whole: FPState, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): IntValue =
                            when (o1) {
                                is TACSymbol.Const -> this.liftConstant(o1.value)
                                is TACSymbol.Var -> {
                                    if (isFreePointerRead(l.wrapped) && o1 == TACKeyword.MEM64.toVar()) {
                                        (offsets[l.ptr] ?: BigInteger.ZERO).let(IntValue.Companion::Constant)
                                    } else {
                                        input[o1] ?: this.nondet
                                    }
                                }
                            }


                }) {
                    override fun project(l: LTACCmd, w: FPState): TreapMap<TACSymbol.Var, IntValue> = w.offsets
                    override fun forget(
                        lhs: TACSymbol.Var,
                        toStep: TreapMap<TACSymbol.Var, IntValue>
                    ): TreapMap<TACSymbol.Var, IntValue> {
                        return toStep + (lhs to IntValue.Nondet)
                    }
                }
    }

    fun analyze(
        graph: TACCommandGraph,
        lva: LiveVariableAnalysis,
        reachingWriteId: Map<CmdPointer, Int>,
        offsets: Map<CmdPointer, BigInteger>,
        knownScratch: Set<CmdPointer>,
        fakeAllocWriteLoc: Map<CmdPointer, AllocationAnalysis.FakeAllocSort>,
        initialFreePointerVal: BigInteger,
    ) = ScratchAnalysisWorker(
            graph = graph,
            offsets = offsets.toTreapMap(),
            knownScratch = knownScratch.toTreapSet(),
            lva = lva,
            reachingWriteId = reachingWriteId.toTreapMap(),
            fakeAllocWriteLoc = fakeAllocWriteLoc.toTreapMap(),
            initialFreePointerVal = initialFreePointerVal,
    ).submit(graph.rootBlocks.map { it.id })
}
