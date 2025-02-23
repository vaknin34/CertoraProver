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

package analysis.opt

import analysis.*
import analysis.numeric.linear.*
import analysis.numeric.linear.TermMatching.matchesAny
import analysis.worklist.IWorklistScheduler
import analysis.worklist.MonadicStatefulParallelWorklistIteration
import analysis.worklist.NaturalBlockScheduler
import analysis.worklist.ParallelStepResult
import com.certora.collect.*
import config.Config
import datastructures.stdcollections.*
import evm.EVM_WORD_SIZE
import parallel.ParallelPool
import spec.CVLKeywords
import spec.toVar
import tac.NBId
import utils.*
import vc.data.*
import vc.data.tacexprutil.TACExprFreeVarsCollector
import java.math.BigInteger
import java.util.stream.Collectors
import java.util.stream.Stream

object PointerSimplification {
    private data class CommuteSpec(
            val firstAdd: ExprView<TACExpr.Vec.Add>,
            val secondAdd: ExprView<TACExpr.Vec.Add>,
            val base: TACSymbol.Var,
            val const: BigInteger,
            val other: TACSymbol.Var,
            val otherUses: MutableMap<CmdPointer, Pair<BigInteger, TACSymbol.Var>>
    )

    private val keywordVars: Set<TACSymbol.Var> = TACKeyword.values().map {
        it.toVar()
    }.toSet() + CVLKeywords.values().map {
        it.toVar()
    }

    fun simplify(p: CoreTACProgram): CoreTACProgram {
        var it = p
        var changed = true
        while(changed) {
            changed = false
            val toRewrite = LinearSimplification.getSimplifications(it).filter {
                /*
                   The storage analysis *very* much relies on the (potentially) redundant assignment to tacM0x0 being
                   around before the hash. So, let's special case this here!
                 */
                it.second !is LinearSimplification.Worker.Rewrite.Remove || it.first.cmd.lhs != TACKeyword.MEM0.toVar()
            }
            if(toRewrite.isNotEmpty()) {
                changed = true
                it = it.patching {
                    for((w, rewrite) in toRewrite) {
                        if (rewrite is LinearSimplification.Worker.Rewrite.Remove) {
                            it.replaceCommand(w.ptr, listOf())
                        } else {
                            it.replaceCommand(w.ptr, listOf(
                                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                            w.cmd.lhs,
                                            rhs = when (rewrite) {
                                                is LinearSimplification.Worker.Rewrite.Const -> rewrite.c.asTACSymbol().asSym()
                                                is LinearSimplification.Worker.Rewrite.Direct -> rewrite.x.asSym()
                                                is LinearSimplification.Worker.Rewrite.Add -> TACExpr.Vec.Add(
                                                        rewrite.v.asSym(),
                                                        rewrite.c.asTACSymbol().asSym()
                                                )
                                                is LinearSimplification.Worker.Rewrite.Linear -> rewrite.x as TACExpr
                                                is LinearSimplification.Worker.Rewrite.Remove -> `impossible!`
                                            }
                                    )
                            ))
                        }
                    }
                }
            }
            // Accessing this early prevents some problematic lazy initialization recursion; see Lazy.kt
            // Scoping this copy of `use` because `it` will change value later, invalidating this value.
            it.analysisCache.use.let { use ->
                val toRemove = it.parallelLtacStream().mapNotNull { lc ->
                    lc.takeIf { _ ->
                        lc.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && use.useSitesAfter(lc.cmd.lhs, lc.ptr).isEmpty() &&
                                (lc.cmd.lhs.meta.find(TACMeta.SCALARIZATION_SORT) == null && lc.cmd.lhs !in keywordVars)

                    }
                }.collect(Collectors.toList())
                if(toRemove.isNotEmpty()) {
                    changed = true
                    it = it.patching {
                        toRemove.forEach { lc ->
                            it.replaceCommand(lc.ptr, listOf())
                        }
                    }
                }
            }
            val g = it.analysisCache.graph

            // Accessing these early prevents some problematic lazy initialization recursion; see Lazy.kt
            val def = g.cache.def
            val use = g.cache.use
            /*
              find places we want to commute adding 32 (or another constant) with another addition

              Why do we want to do this? well, in several cases, we have some value that we are
              adding to the beginning of the element segment (defined to be the location in memory
              32 bytes after the beginning fo the entire array block, i.e., skipping over the length field).

              For example, we might have an elementOffset, or the size of the entire element segment.
              In these cases, adding to the beginning of the element segment (arrayPointer + 32) gives
              a value of meaning: the end of the array block in memory, a valid element in memory, etc.

              In some cases, the solidity compiler will lose its mind and instead add the value of interest directly
              to the array base pointer, and then add 32 to that result. In these cases, the intermediate value is
              *meaningless* and it's only reasonable representation in an abstract interpretation is "a value that
              if you add 32 to you will get ____". Rather than clutter up the abstract interpretations with such intermediate
              abstractions, we just try to identify where the addition of 32 can be commuted with a base pointer, e.g.
              turning (array + something) + 32 into (array + 32) + something.
             */
            val commutes = it.parallelLtacStream().mapNotNull {
                // Find exp assignments...
                it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()
            }.filter {
                // that are adds...
                it.cmd.rhs is TACExpr.Vec.Add
            }.map {
                it.wrapped.enarrow<TACExpr.Vec.Add>()
            }.filter {
                // where there are two operands, one a constant the other a variable
                it.exp.ls.size == 2 && it.exp.ls.any {
                    it is TACExpr.Sym.Const
                } && it.exp.ls.any {
                    it is TACExpr.Sym.Var
                }
            }.mapNotNull {
                /*
                   For the constant baseAdd...
                 */
                val baseAdd = it.exp.ls.singleOrNull {
                    it is TACExpr.Sym.Var
                }?.let { it as TACExpr.Sym.Var }?.s ?: return@mapNotNull null
                /*
                   Find it's definition site
                 */
                val defSite = def.defSitesOf(baseAdd, it.ptr).singleOrNull() ?: return@mapNotNull null
                val dc = g.elab(defSite)
                check(dc.cmd is TACCmd.Simple.AssigningCmd && dc.cmd.lhs == baseAdd)
                /*
                   If the first addition we found is the only use, we have a potential commute candidate
                 */
                val useSitesAfter = use.useSitesAfter(baseAdd, defSite)
                val constantAddition = it.exp.ls.firstMapped {
                    (it as? TACExpr.Sym.Const)?.s
                }?.value ?: return@mapNotNull null
                val otherUses = mutableMapOf<CmdPointer, Pair<BigInteger, TACSymbol.Var>>()
                for(u in useSitesAfter) {
                    if(u == it.ptr) {
                        continue
                    }
                    val otherUse = g.elab(u).takeIf {
                        it.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && it.cmd.rhs is TACExpr.Vec.Add
                    }?.enarrow<TACExpr.Vec.Add>()?.takeIf {
                        it.exp.ls.all {
                            it is TACExpr.Sym
                        }
                    } ?: return@mapNotNull null
                    val otherOp = otherUse.exp.ls.singleOrNull {
                        !it.equivSym(baseAdd)
                    }?.let { it as? TACExpr.Sym.Const } ?: return@mapNotNull null
                    if(otherOp.s.value >= constantAddition) {
                        otherUses[u] = otherOp.s.value to otherUse.lhs
                    } else {
                        return@mapNotNull null
                    }
                }
                /*
                  If the previous definition is not itself an addition, stop
                 */
                if(dc.cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd || dc.cmd.rhs !is TACExpr.Vec.Add) {
                    return@mapNotNull null
                }
                /*
                  If the previous addition is not an addition between two variables, stop
                 */
                if(!dc.cmd.rhs.ls.all {
                            it is TACExpr.Sym.Var
                        }) {
                    return@mapNotNull null
                }
                /*
                  Find one (and only one) operand that "looks like" a pointer
                 */
                val (likelyPointer, other) = dc.cmd.rhs.ls.map {
                    (it as TACExpr.Sym.Var).s
                }.partition {
                    isLikelyPointer(it, g, dc.ptr)
                }
                /*
                  If none or both looked like a pointer, give up
                 */
                if(likelyPointer.size != 1 || other.size != 1) {
                    return@mapNotNull null
                }
                /*
                  Otherwise, commute
                 */
                CommuteSpec(
                        firstAdd = dc.enarrow(),
                        secondAdd = it,
                        base = likelyPointer.single(),
                        other = other.single(),
                        const = constantAddition,
                        otherUses = otherUses
                )
            }.collect(Collectors.toList())
            if(commutes.isNotEmpty()) {
                changed = true
                it = it.patching {
                    for(c in commutes) {
                        it.replaceCommand(c.firstAdd.ptr, listOf(TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = c.firstAdd.lhs,
                                rhs = TACExpr.Vec.Add(
                                        c.base.asSym(), c.const.asTACSymbol().asSym()
                                )
                        )))
                        it.replaceCommand(c.secondAdd.ptr, listOf(TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = c.secondAdd.lhs,
                                rhs = TACExpr.Vec.Add(
                                        c.firstAdd.lhs.asSym(), c.other.asSym()
                                )
                        )))
                        for((otherPointer, otherUse) in c.otherUses) {
                            it.replaceCommand(otherPointer, listOf(TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                    lhs = otherUse.second,
                                    rhs = TACExpr.Vec.Add(
                                            (otherUse.first - c.const).asTACSymbol().asSym(), c.secondAdd.lhs.asSym()
                                    )
                            )))
                        }
                    }
                }
            }
        }
        return it
    }

    private fun isLikelyPointer(p: TACSymbol.Var, g: TACCommandGraph, where: CmdPointer): Boolean {
        return g.cache.def.defSitesOf(p, where).any {
            val lc = g.elab(it)
            (lc.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && lc.cmd.rhs is TACExpr.Sym.Var && lc.cmd.rhs.s == TACKeyword.MEM64.toVar()) ||
                    g.cache.use.useSitesAfter(p, it).any {
                        val useLc = g.elab(it)
                        useLc.cmd is TACCmd.Simple.DirectMemoryAccessCmd && useLc.cmd.loc == p
                    }
        }
    }

    /**
        Rewrites computations to be "simpler". This class runs a *very* simple static analysis to compute the
        linear equalities known to be true at each point in the program. To keep the analysis tractable, these
        linear equalities are not saturated (so we don't derive v1 = v2 + 32 from v1 = v2 + v3 and v3 = 32)
        and we limit the number of variables in each linear equality to 3 (i.e., each linear equality is in terms
        of two other variables and a constant, making the results easy to use in our TAL).

        Afterwards, candidates for rewriting are identified. These candidates are those that are an addition of some constant,
        or use a linear intermediate (explained below)

        For each of these rewrites, the linear equalities generated at each point are consulted for "better" (according to
        a heuristic I made up) definitions, or are removed if the assignment is actually redundant (e.g., v1 = 3; v1 = 3)
    */
    private object LinearSimplification {
        class Worker(private val g: TACCommandGraph) : ArrayLengthHeuristicMixin {
            private val state = mutableMapOf<NBId, LinearInvariants>()

            private val cmdState = mutableMapOf<CmdPointer, LinearInvariants>()

            val useAnalysis = g.cache.use

            /**
             * A linear intermediate is any variable defined by a linear expression (which I take to mean binop or vec op)
             * that is exclusively used in other linear expressions (i.e., binops or vecops). The idea being these variables
             * are prime candidates for rewriting.
             */
            private val linearIntermediates = g.commands.parallelStream().mapNotNull {
                it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.takeIf {
                    it.cmd.rhs is TACExpr.BinOp || it.cmd.rhs is TACExpr.Vec
                }?.takeIf {
                    val use = useAnalysis.useSitesAfter(it.cmd.lhs, it.ptr)
                    use.all {
                        g.elab(it).maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.cmd?.rhs.let {
                            (it is TACExpr.Vec.Add &&
                                !(it.ls.size == 2 && it.operandsAreSyms() && it.ls.any {
                                    it == BigInteger.ZERO.asTACExpr
                                })
                            ) || it is TACExpr.BinOp.Sub
                        }
                    }
                }
            }.collect(Collectors.groupingBy {
                it.cmd.lhs
            }).filterValues {
                it.size == 1
            }.mapValues {
                it.value.single()
            }

            private val allLhs = linearIntermediates.keys.toTreapSet()

            val rewrites : List<Pair<LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>, Rewrite>>

            init {
                g.rootBlocks.forEach {
                    state[it.id] = treapSetOf()
                }
                runAnalysis()
                for((b, inv) in state) {
                    val mInv = inv.builder()
                    for(lc in g.elab(b).commands) {
                        cmdState[lc.ptr] = mInv.build()
                        stepCommand(lc, mInv)
                    }
                }
                rewrites = computeRewrites()
            }

            private fun computeRewrites(): List<Pair<LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>, Rewrite>> {
                // find all assignments
                val str = g.commands.stream().mapNotNull {
                    it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()
                }.filter {
                    it.ptr.block !in g.cache.revertBlocks
                }.filter {
                    // that are additions or subtractions with symbol operands, one of which is a linear intermediate or a constant
                    val rhs = it.cmd.rhs
                    ((rhs is TACExpr.Vec.Add && rhs.ls.size == 2)|| rhs is TACExpr.BinOp.Sub) &&
                            (rhs as TACExpr.BinExp).operandsAreSyms() && listOf((rhs.o1 as TACExpr.Sym).s, (rhs.o2 as TACExpr.Sym).s).any {
                        it is TACSymbol.Const || it in linearIntermediates
                    }
                }.mapNotNull { stmt ->
                    // find a better option if we can
                    val rhs = stmt.cmd.rhs
                    val fv = TACExprFreeVarsCollector.getFreeVars(rhs)
                    val state = cmdState[stmt.ptr] ?: return@mapNotNull null
                    // the cmdState holds the *PRE* state, so it won't actually hold the definitions for lhs of this assignment
                    // so we do a "mini" step here to find all the alternative definitions
                    val altDefs = treapSetOf<LinearEquality>().mutate { altDefs ->
                        for(i in state) {
                            if(i.canGenFor(fv, lhs = stmt.cmd.lhs)) {
                                altDefs.addAll(i.gen(stmt.cmd.lhs, rhs))
                            }
                        }
                    }

                    /* If this is using a "protected" variable, don't simplify it*/
                    if (Config.Foundry.get() && fv.any { TACMeta.FOUNDRY_PROTECTED in it.meta }) {
                        return@mapNotNull null
                    }

                    fun usedAsWriteToFreePointer(v: TACSymbol.Var, ctxt: LTACCmd) : Boolean {
                        val succ = g.succ(ctxt.ptr).singleOrNull() ?: return false
                        return g.cache.use.useSitesAfter(v, ctxt.ptr).any {
                            val store = g.elab(it).maybeNarrow<TACCmd.Simple.AssigningCmd.ByteStore>() ?: return@any false
                            val writtenVal = store.cmd.value as? TACSymbol.Var ?: return@any false
                            store.cmd.loc in g.cache.gvn.equivBefore(it, TACKeyword.MEM64.toVar()) && v in g.cache.gvn.findCopiesAt(succ, store.ptr to writtenVal)
                        }
                    }

                    fun isWordSizeSubtractAnd(v: TACSymbol.Var, ctxt: LTACCmd, k: (TACSymbol.Var, l: LTACCmd) -> Boolean) : Boolean {
                        val succ = g.succ(ctxt.ptr).singleOrNull() ?: return false
                        return g.cache.use.useSitesAfter(v, ctxt.ptr).any { useSite ->
                            val useInAssign = g.elab(useSite).maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>() ?: return@any false
                            val useInSub = useInAssign.cmd.rhs as? TACExpr.BinOp.Sub ?: return@any false
                            useInSub.o2.equivSym(EVM_WORD_SIZE.asTACSymbol()) && (useInSub.o1 as? TACExpr.Sym.Var)?.let { v1 ->
                                v in g.cache.gvn.findCopiesAt(succ, useSite to v1.s)
                            } == true && k(useInAssign.cmd.lhs, g.elab(useSite))
                        }
                    }

                    /*
                      Is this a packed byte length computation, i.e. (endPointer - basePointer) - 32? Then skip this, we don't want
                      something like a constant write or endPointer - elemStartPointer because the alloc is very
                      picky about the patterns it recognizes
                     */
                    val potentialPackedLenComputation = altDefs matchesAny {
                        stmt.cmd.lhs `=` (v("end_ptr") - v("fp") { fpCand ->
                            fpCand is LVar.PVar && fpCand.v in g.cache.gvn.equivBefore(stmt.ptr, TACKeyword.MEM64.toVar())
                        })
                    } != null && (usedAsWriteToFreePointer(stmt.cmd.lhs, stmt.wrapped) || isWordSizeSubtractAnd(stmt.cmd.lhs, stmt.wrapped, ::usedAsWriteToFreePointer))

                    if(potentialPackedLenComputation && altDefs matchesAny {
                            stmt.cmd.lhs `=` k("const")
                        } == null) {
                        // this is a byte array length computation. let's not confuse the alloc!
                        return@mapNotNull null
                    }
                    /*
                      Is this a computation for the new free pointer (i.e. fp + c)? Then don't rewrite it...
                     */
                    if(rhs is TACExpr.Vec.Add && rhs.operandsAreSyms() && rhs.ls.any {
                                it is TACExpr.Sym.Var && it.s in g.cache.gvn.equivBefore(stmt.ptr, TACKeyword.MEM64.toVar())
                            } && rhs.ls.any {
                                it is TACExpr.Sym.Const
                            } && g.cache.use.useSitesAfter(stmt.cmd.lhs, stmt.ptr).any {
                                g.elab(it).let {
                                    it.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && it.cmd.rhs is TACExpr.Sym.Var && it.cmd.lhs == TACKeyword.MEM64.toVar()
                                }
                    }) {
                        return@mapNotNull null
                    }
                    if(rhs is TACExpr.Vec.Add && rhs.operandsAreSyms() && rhs.ls.any {
                        it is TACExpr.Sym.Var && plausibleLengthComponent(
                            g = g, v = it.s, where = stmt.ptr
                        )
                        }) {
                        return@mapNotNull null
                    }
                    /*
                       Now find the "best" representation! Here is how we try to simplify (this is all heuristic based, yeet)
                       1. A single constant
                       2. A single (non-intermediate) variable
                       3. An addition of a constant to a non-intermediate variable (break ties by "smaller" constants)
                       4. A binary term over two non-intermediate variables

                       The above is the preference order for how we simplify existing linear computations. The actual operations
                       we rewrite are selected (and described) above in the first filter

                       A couple of caveats
                       We only replace something with subtraction if the original expression was a subtraction. When replacing
                       an addition with a constant, if the original constant is evm word aligned, only replace with a constant
                       that is also evm word aligned (32 aligned numbers are very special for the analyses and we don't want
                       to erase them). In other cases, only replace the constant with a constant that shares a factor
                       with the original constant.

                       We seed the process with the current candidate, but only if it doesn't have any linear intermediates
                    */
                    var currCandidate : Rewrite? = if(rhs is TACExpr.Vec.Add && rhs.operandsAreSyms() && rhs.ls.any {
                                it is TACExpr.Sym.Const
                            } && rhs.ls.none {
                                it is TACExpr.Sym.Var && it.s in linearIntermediates
                            }) {
                        val c = rhs.ls.firstMapped {
                            (it as? TACExpr.Sym.Const)?.s?.value
                        }
                        val x = rhs.ls.firstMapped {
                            (it as? TACExpr.Sym.Var)?.s
                        }
                        if(c != null && x != null) {
                            Rewrite.Add(v = x, c = c)
                        } else {
                            null
                        }
                    } else {
                        null
                    }
                    var changed = false
                    fun updateCand(r: Rewrite) {
                        if(currCandidate == null || r.isDefinitelyBetterThan(currCandidate!!)) {
                            currCandidate = r
                            changed = true
                        }
                    }
                    /*
                      We don't want a definition that uses linear intermediates: we have
                      to subtract out the lhs here in case it ITSELF is a linear intermediate
                      (in which case it may be further simplified later)
                     */
                    val noUseSet = allLhs - stmt.cmd.lhs
                    for(d in altDefs) {
                        val exp = d.definingIntEquationFor(stmt.cmd.lhs) ?: continue
                        if(d.relatesAny(noUseSet)) {
                            continue
                        }
                        check(d.relates(stmt.cmd.lhs))
                        when(exp) {
                            is TACExpr.Sym.Const -> updateCand(Rewrite.Const(
                                    exp.s.value
                            ))
                            is TACExpr.Sym.Var -> updateCand(Rewrite.Direct(
                                    x = exp.s
                            ))
                            is TACExpr.BinOp.Sub -> if(exp.operandsAreSyms() && exp.o1 is TACExpr.Sym.Var && exp.o2 is TACExpr.Sym.Var && stmt.cmd.rhs is TACExpr.BinOp.Sub) {
                                updateCand(Rewrite.Linear(exp))
                            }
                            is TACExpr.Vec.Add -> {
                                if(exp.ls.size == 2 && exp.operandsAreSyms()) {
                                    val syms = exp.ls.map {
                                        (it as TACExpr.Sym).s
                                    }
                                    val (v, const) = syms.partition {
                                        it is TACSymbol.Var
                                    }
                                    if(const.isEmpty()) {
                                        check(v.size == 2)
                                        updateCand(Rewrite.Linear(
                                                x = exp
                                        ))
                                    } else {
                                        check(v.size == 1)
                                        check(const.size == 1) {
                                            "Too many constants! the defining int equaltion $exp in $d gave back two constants: $const"
                                        }
                                        val c = (const.single() as TACSymbol.Const).value
                                        val currC = currCandidate
                                        if(c.mod(EVM_WORD_SIZE) == BigInteger.ZERO ||
                                                (currC is Rewrite.Add && currC.c.gcd(c).let {
                                                    it > BigInteger.ONE || c == it
                                                })) {
                                            updateCand(Rewrite.Add(
                                                    c = c,
                                                    v = v.first() as TACSymbol.Var
                                            ))
                                        }
                                    }
                                }
                            }
                            else -> {}
                        }
                    }
                    stmt `to?` currCandidate?.takeIf { changed }
                }
                val str2 = g.commands.parallelStream().mapNotNull {
                    it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()
                }.filter {
                    it.cmd.rhs is TACExpr.Sym.Var
                }.mapNotNull {
                    /* if the rhs is known to be equal to the lhs in the PRE state, then this
                        assignment is redundant, remove it.
                     */
                    val st = cmdState[it.ptr] ?: return@mapNotNull null
                    val rhs = (it.cmd.rhs as TACExpr.Sym.Var).s
                    if(st.implies {
                                !rhs `=` !it.cmd.lhs
                            }) {
                        (it to Rewrite.Remove)
                    } else {
                        null
                    }
                }
                return Stream.concat(str, str2).collect(Collectors.toList())
            }

            sealed class Rewrite {
                abstract fun isDefinitelyBetterThan(other: Rewrite) : Boolean
                data class Const(val c: BigInteger) : Rewrite() {
                    override fun isDefinitelyBetterThan(other: Rewrite): Boolean {
                        return other !is Const && other !is Remove
                    }
                }
                data class Direct(val x: TACSymbol.Var) : Rewrite() {
                    override fun isDefinitelyBetterThan(other: Rewrite) : Boolean {
                        return other is Add || other is Linear
                    }
                }
                data class Add(val v: TACSymbol.Var, val c: BigInteger) : Rewrite() {
                    override fun isDefinitelyBetterThan(other: Rewrite): Boolean {
                        return (other is Linear || (other is Add && other.c > this.c))
                    }
                }
                data class Linear(val x: TACExpr.BinExp) : Rewrite() {
                    override fun isDefinitelyBetterThan(other: Rewrite): Boolean {
                        if(other is Linear && other.x is TACExpr.BinOp.Sub && this.x is TACExpr.Vec.Add) {
                            return true
                        }
                        return false
                    }
                }
                object Remove : Rewrite() {
                    override fun isDefinitelyBetterThan(other: Rewrite): Boolean = true
                }
            }

            private fun runAnalysis() {
                object : MonadicStatefulParallelWorklistIteration<NBId, Pair<NBId, LinearInvariants>, Unit, Unit>(
                  inheritPool = (Thread.currentThread() as? ParallelPool.ParallelPoolWorkerThread)?.parallelPool
                ) {
                    override val scheduler: IWorklistScheduler<NBId> = NaturalBlockScheduler(g)

                    override fun commit(c: Pair<NBId, LinearInvariants>, nxt: MutableCollection<NBId>, res: MutableCollection<Unit>) {
                        val (where, inv) = c
                        if(where in g.cache.revertBlocks) {
                            return
                        }
                        if(where !in state) {
                            state[where] = inv
                            nxt.add(where)
                            return
                        }
                        val curr = state[where]!!
                        val joined =  curr.fastJoin(inv)
                        if(joined != curr) {
                            state[where] = joined
                            nxt.add(where)
                        }
                    }

                    override fun reduce(results: List<Unit>) {
                    }

                    override fun process(it: NBId): ParallelStepResult<Pair<NBId, LinearInvariants>, Unit, Unit> {
                        val currInv = state[it]!!.mutate { currInv ->
                            val block = g.elab(it)
                            for(c in block.commands) {
                                stepCommand(c, currInv)
                            }
                            // keep only those invariants that mention at least one live variable and have fewer than three
                            // variables used
                            val lva = g.cache.lva.liveVariablesAfter(block.commands.last().ptr).toTreapSet()
                            currInv.retainAll {
                                it.term.size <= 3 &&
                                it.pvars.containsAny(lva)
                            }
                        }
                        return ParallelStepResult.ContinueWith(g.succ(it).map {
                            it to currInv
                        })
                    }
                }.submit(g.rootBlocks.map { it.id })
            }


            fun isPointerSizeComparison(l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>) : Boolean =
                    l.takeIf {
                        val rhs = it.cmd.rhs
                        rhs is TACExpr.Vec.Add && rhs.ls.any {
                            it is TACExpr.Sym.Const && it.s.value.mod(EVM_WORD_SIZE) == 31.toBigInteger()
                        }
                    }?.let {
                        val lhs = it.cmd.lhs
                        g.cache.use.useSitesAfter(lhs, it.ptr).singleOrNull()?.let(g::elab)?.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.let {
                            val r = it.cmd.rhs
                            r is TACExpr.BinRel.Slt && r.o1 is TACExpr.Sym.Var && r.o1.s == lhs
                        } == true
                    } ?: false

            private fun stepCommand(c: LTACCmd, currInv: MutableSet<LinearEquality>) {
                if (c.cmd !is TACCmd.Simple.AssigningCmd) {
                    return
                }
                if (c.cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
                    currInv.removeIf {
                        it.relates(c.cmd.lhs)
                    }
                    return
                }
                val cmd = c.cmd
                val exp = cmd.rhs
                val freeVars = TACExprFreeVarsCollector.getFreeVars(exp)
                val toAdd = mutableSetOf<LinearEquality>()
                if(c.cmd.lhs == TACKeyword.MEM64.toVar()) {
                    currInv.removeIf {
                        it.relatesAny(freeVars) || it.relates(cmd.lhs)
                    }
                    return
                }
                /* don't generate anything if this looks like a pointer size comparison
                   defined to be adding 31 to a variable and then immediately using that
                   in a comparison
                 */
                if(isPointerSizeComparison(c.narrow())) {
                    return
                }
                if (TACKeyword.MEM64.toVar() !in freeVars && c.cmd.lhs != TACKeyword.MEM64.toVar()) {
                    val t = LinearTerm.lift(cmd.rhs)
                    if (t != null) {
                        toAdd.add(LinearEquality.build {
                            !cmd.lhs `=` t
                        })
                    }
                }
                for (i in currInv) {
                    if (!i.canGenFor(freeVars, cmd.lhs)) {
                        continue
                    }
                    toAdd.addAll(i.gen(cmd.lhs, exp))
                }
                currInv.removeIf {
                    it.relates(cmd.lhs)
                }
                currInv.addAll(toAdd)
            }
        }

        fun getSimplifications(p: CoreTACProgram) = Worker(g = p.analysisCache.graph).rewrites
    }
}
