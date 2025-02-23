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

package instrumentation.transformers

import analysis.*
import analysis.numeric.linear.LVar
import analysis.numeric.linear.LinearEquality
import analysis.numeric.linear.LinearTerm
import com.certora.collect.*
import datastructures.stdcollections.*
import tac.Tag
import utils.firstMapped
import utils.mapNotNull
import vc.data.*
import java.math.BigInteger

/**
 * This works around an unfortunate optimization performed by the Solidity compiler for allocations
 * of structs with nested arrays.
 *
 * Given
 *
 * struct Foo {
 *    Bar x;
 *    ...
 *  }
 *  struct Bar {
 *    uint a;
 *    uint b;
 *    ...
 *  }
 *
 *  the solidity compiler will (sometimes) generate:
 *  ```
 *  base = fp
 *  fp = base + sizeof(Foo) + sizeof(Bar);
 *  mem[base + sizeof(Foo] = 0; // init Bar.a
 *  mem[base + sizeof(Foo) + 32] = 0; // init Bar.b;
 *  ...
 *  mem[base] = base + sizeof(Foo);
 *  ```
 *
 *  This *ruins* the PTA, but probably not for the reason you think: the initialization analysis expects structs to be allocated
 *  "in order", so the initialization of the single, too large struct in base never completes. tanking the init analysis.
 *
 *  This peephole de-optimizer targets this pattern, by first identifying all constant struct allocations. For
 *  each such allocation site, it proceeds as follows
 *  First, it finds the suffix of command within the block starting from the allocation which is:
 *  1. allocation free, and
 *  2. variable reuse free
 *
 *  The second isn't fundamental, but it simplifies our reasoning.
 *
 *  It then finds a write within that suffix where the location being written to is within the newly created block,
 *  and the value being written is also a field within the block. Further, it checks that the field pointer being
 *  written is "later" in the buffer from the location at which that write occurs. We take this to be the "recursive write"
 *  pattern.
 *
 *  We then look at the prefix up to the point of the recursive write to check that all such writes must come
 *  **after** the field pointer being written. We then record the "correct" field offsets for the locations being
 *  written (as opposed to locations which are relative to the beginning of the smashed together alloc). We also
 *  record `size_of_alloc - field_offset` as the inferred size of the sub-struct whose allocation was folded
 *  into the parent struct.
 *
 *  We actually then repeat this process on the remaining suffix commands, recursively until we run out of commands to check.
 *  At each step, we decrease the `size_of_alloc` to reflect that the large, smashed together buffer is shrinking is size
 *  as we process more commands.
 *
 *  Then we rewrite the original program: the original allocation is sliced up into the appropriately sized chunks
 *  as computed previously. The field writes for the sub-structs are then rewritten in terms of the new allocs and the
 *  "corrected" field structs.
 *
 *  Note that if we infer incorrectly and this pattern doesn't match what we expect (maybe in the sub-struct initialization
 *  prefix not all fields were written), we will still conservatively fail the analysis
 *  and, because we are *very* careful to preserve the order of allocations and the ultimate layout of data
 *  in memory, shouldn't change the semantics of the program.
 */
object StructAllocationDeoptimizer {
    private val constantStructAlloc = PatternDSL.build {
        (Var { v, where ->
            if(v == TACKeyword.MEM64.toVar()) {
                PatternMatcher.VariableMatch.Match(where)
            } else {
                PatternMatcher.VariableMatch.Continue
            }
        } + Const).commute.withAction { where, memRead, k ->
            Triple(memRead, k, where)
        }
    }

    private data class MatchPayload(
        val pointerWriteLocation: LTACCmd,
        val pointerReadLocation: LTACCmd,
        val addLocation: LTACCmd,
        val allocationAmount: BigInteger
    )

    fun rewrite(c: CoreTACProgram) : CoreTACProgram {
        val matcher = PatternMatcher.compilePattern(c.analysisCache.graph, constantStructAlloc)
        val concurrent = ConcurrentPatchingProgram(c)
        c.parallelLtacStream().filter {
            it.cmd is TACCmd.Simple.AssigningCmd && it.cmd.lhs == TACKeyword.MEM64.toVar()
        }.mapNotNull { write ->
            matcher.queryFrom(write.narrow()).toNullableResult()?.let {
                MatchPayload(
                    pointerReadLocation = it.first,
                    addLocation = it.third,
                    pointerWriteLocation = write,
                    allocationAmount = it.second
                )
            }
        }.filter { m ->
            /* all within the same block, and ordered sanely. The ordered sanely kind of has to follow from the pattern
               we match on, but best to be explicit
             */
            m.addLocation.ptr.block == m.pointerReadLocation.ptr.block && m.pointerReadLocation.ptr.block == m.pointerWriteLocation.ptr.block &&
                m.addLocation.ptr.pos < m.pointerWriteLocation.ptr.pos && m.pointerReadLocation.ptr.pos < m.addLocation.ptr.pos
        }.mapNotNull { payload ->
            deOptimizeAlloc(
                payload, c
            )?.let {
                RewriteInstrumentation(
                    c, payload, it
                )
            }
        }.forEach {
            for((ptr, rewrite) in it.rewrites) {
                concurrent.replace(ptr, rewrite)
            }
            concurrent.addVarDecls(it.newVars)
        }
        return concurrent.toCode()
    }

    private class RewriteInstrumentation(
        private val c: CoreTACProgram,
        private val payload: MatchPayload,
        r: Rewrite
    ) {
        private val graph = c.analysisCache.graph

        /**
         * Commands to insert after the original alloc (these will effect the "sub-struct" allocations)
         */
        private val extraAllocCommands = mutableListOf<TACCmd.Simple>()
        private val tempVars = mutableSetOf<TACSymbol.Var>()

        /**
         * A local version of the patching program, this gets put into the single concurrent patcher in the main driver
         * [rewrite]
         */
        private val commandReplacements = mutableMapOf<CmdPointer, List<TACCmd.Simple>>()

        /**
         * The [rewrittenBase] argument indicates that the write at the first portion of the tuple
         * is a recursive write of a sub-struct into the parent struct. Thus when doing the rewrites
         * within this invocation, that write's value should be replaced with the second part of the tuple,
         * which is the variable that holds the new variable that is the result of the allocation.
         */
        private fun rewrite(
            r: Rewrite?,
            rewrittenBase: Pair<CmdPointer, TACSymbol.Var>?,
            remainingSpace: BigInteger
        ) {
            /**
             * Because of how the rewrite objects are collected, the "outer" Rewrite object will be the
             * first sub struct, it's next field will be the second sub struct, etc.
             *
             * Notice that the pattern requires that the first sub struct is also the innermost struct, and must be allocated
             * **last**, the second substruct is the next level up, and must be allocated second, etc.
             *
             * Thus, when we reach this point (where r == null) then this is the case where what we think is the outer most
             * struct, for which the allocation "should" be. Thus, the remainingSpace parameteter is the actual size of
             * this outermost struct (again,
             * computed by slicing off the sizes of all the inner structs which were processed before this point)
             */
            if(r == null) {
                /**
                 * rewrittenBase must be non-null here because every recursive call with a possible null [r] parameter
                 * must pass a non-null value for [rewrittenBase]
                 */
                check(remainingSpace > BigInteger.ZERO && rewrittenBase != null) {
                    "Something went bad TODO: better error"
                }
                val subAllocWrite = c.analysisCache.graph.elab(rewrittenBase.first).narrow<TACCmd.Simple.AssigningCmd.ByteStore>()
                val fpBump = getTemp()
                add(payload.addLocation.ptr, listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = fpBump,
                        rhs = TACExpr.Vec.Add(
                            payload.pointerReadLocation.narrow<TACCmd.Simple.AssigningCmd>().cmd.lhs.asSym(),
                            remainingSpace.asTACExpr
                        )
                    )
                ))
                /**
                 *  Rewrite the original allocation to be the correct size (determined by how many bytes are left
                 *  over after all substructs have been allocated)
                 */
                replace(payload.pointerWriteLocation.ptr, listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = TACKeyword.MEM64.toVar(),
                        rhs = fpBump.asSym()
                    )
                ))
                /* Rewrite the store of the first-substruct to point to the variable given by the
                * freshly instrumented allocation (which was done in our caller)
                */
                replace(subAllocWrite.ptr, listOf(
                    subAllocWrite.cmd.copy(
                        value = rewrittenBase.second
                    )
                ))
                return
            }
            /**
             * Then we are a substruct that will be written later into a parent struct.
             * freshAlloc holds the newly instrumented variable which will hold the result
             * of a separate allocation of the size given by `r.allocSize`
             */
            val freshAlloc = getTemp()
            val freshBump = getTemp()
            rewrite(
                r = r.next,
                /*
                  Indicate that when writing the reference to **this** substruct at the recursive write location,
                  use the newly generated pointer instead.
                 */
                rewrittenBase = r.subAllocWrite.ptr to freshAlloc,
                remainingSpace = remainingSpace - r.allocSize
            )
            /**
             * The ordering here is important: because the inner most sub-struct (i.e., the **outermost**
             * [Rewrite] instance) must be allocated last, we add the allocation commands after our recursive
             * call has completed (so our parent structs can be allocated first)
             */
            extraAllocCommands.addAll(listOf(
                exp {
                    freshAlloc `=` TACKeyword.MEM64.toVar()
                },
                exp {
                    freshBump `=` TACExpr.Vec.Add(
                        freshAlloc.asSym(),
                        r.allocSize.asTACExpr
                    )
                },
                exp {
                    TACKeyword.MEM64.toVar() `=` freshBump
                }
            ))
            /*
             * Someone told us to rewrite a recursive write to point to a newly generated location,
             * but we need to know about that field first.
             */
            if(rewrittenBase != null) {
                require(rewrittenBase.first in r.writes)
            }
            for((where, offset) in r.writes) {
                val newLoc = getTemp()
                val writeCommand = graph.elab(where).narrow<TACCmd.Simple.AssigningCmd.ByteStore>()
                /*
                 As in the base case, if this is recursive write location, then we must use the pointer to the separately
                 allocated child struct.
                 */
                val newValue = if(where == rewrittenBase?.first) {
                    rewrittenBase.second
                } else {
                    writeCommand.cmd.value
                }
                replace(where, listOf(
                    exp {
                        newLoc `=` freshAlloc + offset.asTACSymbol()
                    },
                    writeCommand.cmd.copy(
                        value = newValue,
                        loc = newLoc
                    )
                ))
            }
        }

        private fun add(ptr: CmdPointer, what: List<TACCmd.Simple>) {
            require(ptr !in commandReplacements) {
                "double replacing"
            }
            commandReplacements[ptr] = listOf(c.analysisCache.graph.elab(ptr).cmd) + what
        }

        private fun replace(ptr: CmdPointer, what: List<TACCmd.Simple>) {
            require(ptr !in commandReplacements) {
                "Double replacing some write, something has goofed bad"
            }
            commandReplacements[ptr] = what
        }

        private fun getTemp() = TACKeyword.TMP(Tag.Bit256, "!alloc").toUnique("!").also {
            tempVars.add(it)
        }

        init {
            rewrite(
                r = r,
                rewrittenBase = null,
                remainingSpace = payload.allocationAmount
            )
        }

        val rewrites : TreapMap<CmdPointer, List<TACCmd.Simple>> = run {
            val ret = commandReplacements.toTreapMap()
            ret + (payload.pointerWriteLocation.ptr to (commandReplacements[payload.pointerWriteLocation.ptr].orEmpty() + extraAllocCommands))
        }

        val newVars = tempVars.toTreapSet()
    }

    data class Rewrite(
        val allocSize: BigInteger,
        val writes: Map<CmdPointer, BigInteger>,
        val subAllocWrite: LTACCmdView<TACCmd.Simple.AssigningCmd.ByteStore>,
        val next: Rewrite?
    )

    /**
     * [c] the parent program.
     * [commands] a list of commands to scan for the recursive write pattern.
     * [remainingSpace] how much space remains of [MatchPayload.allocationAmount] after
     * previously processed commands have sliced off sub structs.
     */
    private fun deOptimizeAlloc(payload: MatchPayload, c: CoreTACProgram, commands: List<LTACCmd>, remainingSpace: BigInteger) : Rewrite? {
        /**
         * Try to determine the constant offset of [v] w.r.t to the free pointer **before** the allocation.
         * If found (and if within the allocated buffer) this gives the field being written within the object.
         */
        fun getOffsetFromFPAt(v: TACSymbol.Var, where: CmdPointer) : BigInteger? {
            val vDef = DefiningEquationAnalysis.getDefiningEquation(
                g = c.analysisCache.graph,
                where = where,
                target = payload.pointerReadLocation.ptr,
                v = v
            ) ?: return null
            val offsetFromFP = LinearTerm.lift(
                TACExpr.BinOp.Sub(
                    vDef,
                    TACKeyword.MEM64.toVar().asSym()
                )
            ) ?: return null

            /**
             * effectively simplify exp - fp. If v is defined as `fp + k`, this will just leave
             * k, which we can extract later.
             *
             * Is there a simpler way to compute this? I'm not really sure, given that the `k` could be
             * built up through several intermediate additions, we really kind of want the egraphs-lite
             * that [LinearEquality] gives us.
             */
            val eq = LinearEquality.build {
                LVar.Instrumentation("offs") `=` offsetFromFP
            }.canonicalize()
            /*
              Using the term matcher here would be unnecessarily expensive for
              what is a very simple check.
             */
            if(eq.term.keys.singleOrNull() != LVar.Instrumentation("offs")) {
                return null
            }
            return if(eq.k == BigInteger.ZERO) {
                BigInteger.ZERO
            /**
             * Different polarities, i.e. c * offs = k
             */
            } else if((eq.k < BigInteger.ZERO) == (eq.term.values.single() < BigInteger.ZERO)) {
                null
            /**
             * and c == 1
             */
            } else if(eq.term.values.single().abs() != BigInteger.ONE) {
                null
            } else {
                // so offset = k, that is, v = fp + k
                eq.k.abs()
            }
        }
        val (recursiveWrite, subAllocStart) = commands.firstMapped { lc ->
            if(lc.cmd !is TACCmd.Simple.AssigningCmd.ByteStore ||
                lc.cmd.value !is TACSymbol.Var ||
                lc.cmd.loc !is TACSymbol.Var ||
                lc.cmd.base != TACKeyword.MEMORY.toVar()) {
                return@firstMapped null
            }
            val locOffset = getOffsetFromFPAt(
                v = lc.cmd.loc,
                where = lc.ptr
            ) ?: return@firstMapped null
            val valueOffset = getOffsetFromFPAt(
                v = lc.cmd.value,
                where = lc.ptr
            ) ?: return@firstMapped null
            /**
             * That is, we've found a write `mem[l] = v` where l = fp + c and v = fp + d and c < d
             */
            if(!(locOffset < remainingSpace && valueOffset < remainingSpace && locOffset < valueOffset)) {
                return@firstMapped null
            }
            lc to valueOffset
        } ?: return null
        val precedingWrites = commands.asSequence().takeWhile {
            it.ptr != recursiveWrite.ptr
        }.mapNotNull {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd.ByteStore>()?.takeIf {
                it.cmd.base == TACKeyword.MEMORY.toVar()
            }
        }.toList()
        check(precedingWrites.size < commands.size)
        val preceding = mutableMapOf<CmdPointer, BigInteger>()
        for(pw in precedingWrites) {
            if(pw.cmd.loc !is TACSymbol.Var) {
                return null
            }
            /*
              all writes in the prefix up to the recursive write should also be of the form
              mem[l] = v where l = fp + k
             */
            val offs = getOffsetFromFPAt(
                v = pw.cmd.loc as TACSymbol.Var,
                where = pw.ptr
            ) ?: return null
            /*
              If k is not "after" sub alloc start within the buffer, something *very* strange is going
              on, bail out
             */
            if(offs !in subAllocStart..remainingSpace) {
                return null
            }
            preceding[pw.ptr] = offs - subAllocStart
        }
        val writeInd = commands.indexOfFirst {
            it.ptr == recursiveWrite.ptr
        }
        check(writeInd > -1)
        val nxt = if(writeInd == commands.lastIndex) {
            null
        } else {
            /*
              subAllocStart becomes the new "size" of the buffer, writes after this point
              should all have already been seen at this point. Recursively check the remainder of the commands
             */
            deOptimizeAlloc(
                payload, c, commands.subList(writeInd, commands.lastIndex), subAllocStart
            )
        }
        return Rewrite(
            remainingSpace - subAllocStart,
            preceding,
            subAllocWrite = recursiveWrite.narrow(),
            next = nxt
        )
    }

    private fun deOptimizeAlloc(payload: MatchPayload, c: CoreTACProgram): Rewrite? {
        /* take all commands (up to the end of the block) that do not touch the free pointer
         */
        val allocFreeSuffix = c.analysisCache.graph.iterateBlock(payload.pointerWriteLocation.ptr, excludeStart = true).takeWhile {
            (it.cmd !is TACCmd.Simple.AssigningCmd || it.cmd.lhs != TACKeyword.MEM64.toVar()) && (TACKeyword.MEM64.toVar() !in it.cmd.getFreeVarsOfRhs())
        }
        val writtenVars = mutableSetOf<TACSymbol.Var>()
        /*
          find those that do not reuse variables
         */
        val variableReuseFreeSuffix = allocFreeSuffix.takeWhile {
            it.cmd !is TACCmd.Simple.AssigningCmd || (it.cmd is TACCmd.Simple.AssigningCmd.ByteStore || writtenVars.add(it.cmd.lhs))
        }
        return deOptimizeAlloc(
            payload = payload,
            c = c,
            commands = variableReuseFreeSuffix,
            remainingSpace = payload.allocationAmount
        )
    }
}
