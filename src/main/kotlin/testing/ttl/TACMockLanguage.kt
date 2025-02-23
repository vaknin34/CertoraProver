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

package testing.ttl

import analysis.TACCommandGraph
import com.certora.collect.*
import tac.*
import utils.*
import vc.data.*
import vc.data.parser.parseExpr
import java.math.BigInteger
import kotlin.reflect.KProperty

data class BuilderVar(val v: TACSymbol.Var)

val MOCK_TAG = MetaKey<String>("mock.command.tag")

@Suppress("unused")
object TACMockLanguage {
    interface ElseScope {
        infix fun `else`(falseBranch: StmtBuilderScope.() -> Unit)
    }

    enum class BlockState {
        Empty,
        Current,
        Inherit,
        Exit,
        ForcePopulate
    }

    class NBIdAlloc {
        fun freshBlock(): NBId {
            return StartBlock.copy(
                origStartPc = nextBlockId++,
                stkTop = 1000
            )
        }

        private var nextBlockId = 0
    }

    /*
     During compilation the builder can be in one of four states:

        1 - have no commands, with the current block (thisId) pending, i.e., it needs a successor

        2 - have no commands, with some inherited pending, i.e., some other blocks have the current block as a successor

        3 - have commands, this current block (thisId) pending, i.e., we have some commands that need a successor block

        4 - have no commands, no pending

     */
    class StmtBuilderScope constructor(
            private val blockGraph: MutableBlockGraph,
            private val blockCmds: MutableMap<NBId, List<TACCmd.Simple>>,
            private var thisId: NBId,
            private val idAlloc: NBIdAlloc,
            private var state: BlockState
    ) {
        val nop: Unit
            get() = pushCommand(TACCmd.Simple.NopCmd)
        /*
          Inherit pending indicates that this block (thisId) is the successor for all blocks in inheritPending.
          If this block has commands pushed into it (i.e., the block will appear in the result program) then
          all blocks in inheritPending should be set to have their successor are thisId
         */
        private val inheritPending = mutableSetOf<NBId>()
        var finished: Boolean = false
        private var pendingTag : String? = null

        class HAVOC private constructor() {
            companion object {
                val inst = HAVOC()
            }
        }

        private inner class StackVarDelegate(private val slot: Int) {
            operator fun getValue(thisRef: StmtBuilderScope, property: KProperty<*>) : Any {
                return thisRef.L(slot)
            }

            operator fun setValue(thisRef: StmtBuilderScope, property: KProperty<*>, value: Any?) {
                check(thisRef === this@StmtBuilderScope)
                if(value is String) {
                    thisRef.L(slot).`=`(value)
                } else if(value is Int) {
                    thisRef.L(slot).`=`(value)
                } else if(value is BigInteger) {
                    thisRef.L(slot).`=`(value)
                } else if(value is BuilderVar) {
                    thisRef.L(slot).`=`(value)
                } else if(value is HAVOC) {
                    thisRef.L(slot) `=` value
                } else if(value is MemRef) {
                    thisRef.L(slot) `=` value
                } else if(value is StorageRef) {
                    thisRef.L(slot) `=` value
                } else {
                    throw RuntimeException("TYPE ERROR $value")
                }
            }
        }

        val mem = MemoryProxy(TACKeyword.MEMORY.toVar())
        val codedata = MemoryProxy(TACKeyword.CODEDATA.toVar().withMeta(TACMeta.CODEDATA_KEY, BigInteger.ZERO))
        val storage = StorageProxy()

        abstract class PersistentProxy {
            protected abstract fun makeSet(where: BuilderVar, v: TACSymbol)

            operator fun set(where: Any, what: Any) {
                if(where !is BuilderVar) {
                    throw ClassCastException("Can only index vars")
                }
                when(what) {
                    is BuilderVar -> {
                        this.makeSet(where, what.v)
                    }
                    is Int -> {
                        this.makeSet(where, TACSymbol.lift(what))
                    }
                    is BigInteger -> {
                        this.makeSet(where, TACSymbol.lift(what))
                    }
                    else -> throw IllegalArgumentException("don't know what to do with $what")
                }
            }

        }

        open inner class MemoryProxy(val base: TACSymbol.Var): PersistentProxy() {
            override fun makeSet(where: BuilderVar, v: TACSymbol) {
                pushCommand(TACCmd.Simple.AssigningCmd.ByteStore(
                        base = base,
                        loc = where.v,
                        value = v
                    )
                )
            }

            operator fun get(where: Any): MemRef {
                return if (where is BuilderVar) {
                    MemRef(base, where.v)
                } else if (where is Int) {
                    MemRef(base, where.asTACSymbol())
                } else {
                    throw java.lang.ClassCastException("Can only read vars or integers, got $where")
                }
            }
        }

        inner class StorageProxy: PersistentProxy() {
            override fun makeSet(where: BuilderVar, v: TACSymbol) {
                pushCommand(TACCmd.Simple.WordStore(
                    base = TACKeyword.STORAGE.toVar().withMeta(TACMeta.STORAGE_KEY, 0.toBigInteger()),
                    loc = where.v,
                    value = v
                ))
            }

            operator fun get(where: Any): StorageRef {
                if(where !is BuilderVar) {
                    throw java.lang.ClassCastException("Can only read vars, got $where")
                }
                return StorageRef(
                    TACKeyword.STORAGE.toVar().withMeta(TACMeta.STORAGE_KEY, 0.toBigInteger()),
                    where.v
                )
            }
        }

        var L1024 by StackVarDelegate(1024)
        var L1023 by StackVarDelegate(1023)
        var L1022 by StackVarDelegate(1022)
        var L1021 by StackVarDelegate(1021)
        var L1020 by StackVarDelegate(1020)


        val freePointer = BuilderVar(TACKeyword.MEM64.toVar())

        @Suppress("DANGEROUS_CHARACTERS")
        val `*` = HAVOC.inst

        private val instrList = mutableListOf<TACCmd.Simple>()
        fun L(v: Int) : BuilderVar = BuilderVar(TACSymbol.Var("L$v", Tag.Bit256))
        fun L(v: Int, tag: Tag) : BuilderVar = BuilderVar(TACSymbol.Var("L$v", tag))
        fun K(v: String) : BuilderVar = BuilderVar(TACKeyword.valueOf(v).toVar())

        infix fun Int.`=`(v: BuilderVar) = L(this) `=` v
        infix fun Int.`=`(v: HAVOC) = L(this) `=` v
        infix fun Int.`=`(i: Int) = L(this) `=` i
        infix fun Int.`=`(i: BigInteger) = L(this) `=` i
        infix fun Int.`=`(i: MemRef) = L(this) `=` i
        infix fun Int.`=`(i: StorageRef) = L(this) `=` i

        infix fun BuilderVar.`=`(v: BuilderVar) {
            pushCommand(TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    this.v,
                    v.v
            ))
        }
        infix fun BuilderVar.`=`(v: HAVOC) {
            unused(v)
            pushCommand(TACCmd.Simple.AssigningCmd.AssignHavocCmd(
                    lhs = this.v,
                    meta = MetaMap()
            ))
        }
        infix fun BuilderVar.`=`(i: Int) {
            pushCommand(TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    this.v,
                    TACSymbol.lift(i)
            ))
        }
        infix fun BuilderVar.`=`(l: BigInteger) {
            pushCommand(TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    this.v,
                    TACSymbol.lift(l)
            ))
        }

        infix fun BuilderVar.`=`(m: MemRef) {
            pushCommand(TACCmd.Simple.AssigningCmd.ByteLoad(
                    lhs = this.v,
                    base = m.base,
                    loc = m.v,
                    meta = MetaMap()
            ))
        }

        infix fun BuilderVar.`=`(m: StorageRef) {
            pushCommand(TACCmd.Simple.AssigningCmd.WordLoad(
                lhs = this.v,
                base = m.base,
                loc = m.v,
                meta = MetaMap()
            ))
        }

        infix fun BuilderVar.`=`(v: String) {
            val expr = v.parseExpr()
            pushCommand(TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    this.v,
                    expr
            ))
        }

        fun `if`(idx: Int, v: String, thenBranch: StmtBuilderScope.() -> Unit) : ElseScope {
            val expr = v.parseExpr()
            val flag = L(idx, Tag.Bool)
            pushCommand(TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    flag.v,
                    expr
            ))
            return this.`if`(flag, thenBranch)
        }

        fun MemCopy(dstOff: BuilderVar, srcOff: BuilderVar, len: BuilderVar) {
            pushCommand(
                TACCmd.Simple.ByteLongCopy(
                    dstOffset = dstOff.v,
                    dstBase = TACKeyword.MEMORY.toVar(),
                    srcOffset = srcOff.v,
                    srcBase = TACKeyword.MEMORY.toVar(),
                    length = len.v,
                    meta = MetaMap()
                )
            )
        }

        private fun pushCommand(toAdd: TACCmd.Simple) {
            this.checkNotFinished()
            this.checkInvariant()
            if(this.state == BlockState.Inherit){
                for(p in this.inheritPending) {
                    wireSuccessors(p, thisId)
                }
                this.inheritPending.clear()
            }
            state = BlockState.Current
            /*
              now in state state 1 or state 3
             */
            if(pendingTag != null) {
                instrList.add(
                        toAdd.mapMeta {
                            it + (MOCK_TAG to pendingTag!!)
                        }
                )
                pendingTag = null
            } else {
                instrList.add(
                        toAdd
                )
            }
            /* now in state 3 */
            this.checkInvariant()
        }

        private fun wireSuccessors(p: NBId, target: NBId) {
            unused(blockGraph.merge(p, treapSetOf(target)) { a, b -> a + b })
            assert(p in blockCmds)
            blockCmds.merge(p, listOf(TACCmd.Simple.JumpCmd(
                    dst = target
            ))) { curr, push ->
                curr + push
            }
        }
        fun `if`(slot: Int, havoc: HAVOC, thenBranch: StmtBuilderScope.() -> Unit) : ElseScope {
            unused(havoc)
            this.pushCommand(TACCmd.Simple.AssigningCmd.AssignHavocCmd(
                    L(slot, Tag.Bool).v
            ))
            return `if`(L(slot, Tag.Bool), thenBranch)
        }

        fun `if`(v: BuilderVar, thenBranch: StmtBuilderScope.() -> Unit) : ElseScope {
            val thenBlockId = idAlloc.freshBlock()
            val elseBlockId = idAlloc.freshBlock()
            blockGraph[thisId] = treapSetOf(thenBlockId, elseBlockId)
            pushCommand(TACCmd.Simple.JumpiCmd(
                    dst = thenBlockId,
                    cond = v.v,
                    meta = MetaMap(),
                    elseDst = elseBlockId
            ))
            /* now we must be in state Current:
               have commands, this id pending
             */
            this.checkInvariant()
            /*
               Add the commands, alloc fresh id, clear this pending (we have a successor, the then and else)
             */
            this.flushBlock()
            /*
               We now have no commands, no pending, no inherited, i.e. state 4
             */
            val thenBuilder = StmtBuilderScope(blockGraph, blockCmds, thenBlockId, idAlloc, BlockState.ForcePopulate)
            thenBuilder.thenBranch()
            thenBuilder.finish(this.inheritPending)
            /*
              add the then branch to pendingNext
              so now, we may be in state 2 (no commands, inherited pending) or state 4 (no commands, no pending)
             */
//            this.checkInvariant()
            return object : ElseScope {
                override fun `else`(falseBranch: StmtBuilderScope.() -> Unit) {
                    val falseBuilder = StmtBuilderScope(blockGraph, blockCmds, elseBlockId, idAlloc, BlockState.ForcePopulate)
                    falseBuilder.falseBranch()
                    falseBuilder.finish(inheritPending)
                    /*
                      From state 4 or state 2, we either go to state 2 or state 4
                     */
                    this@StmtBuilderScope.state = if(inheritPending.isEmpty()) { BlockState.Empty } else {
                        BlockState.Inherit
                    }
                    this@StmtBuilderScope.checkInvariant()
                }
            }
        }

        private fun flushBlock(tgt: NBId? = null) {
            check(instrList.isNotEmpty())
            this.blockCmds[thisId] = instrList.toList()
            instrList.clear()
            thisId = tgt ?: idAlloc.freshBlock()
            state = BlockState.Empty
        }

        private fun checkInvariant() {
            // if we have inherit pending not empty, instrList must be empty
            check(this.inheritPending.isEmpty() || this.instrList.isEmpty())
            check(this.state == BlockState.Inherit || this.inheritPending.isEmpty())
        }

        fun finish(next: MutableSet<NBId>) {
            if(!this.finished) {
                this.finished = true
                when(this.state) {
                    BlockState.Empty -> {
                        // do nothing
                        check(instrList.isEmpty())
                    }
                    BlockState.ForcePopulate -> {
                        check(instrList.isEmpty())
                        instrList.add(TACCmd.Simple.NopCmd)
                        blockCmds[thisId] = instrList
                        next.add(this.thisId)
                    }
                    BlockState.Current -> {
                        check(instrList.isNotEmpty())
                        next.add(this.thisId)
                        blockCmds[thisId] = instrList
                    }
                    BlockState.Inherit -> {
                        check(instrList.isEmpty())
                        next.addAll(inheritPending)
                    }
                    BlockState.Exit -> {
                        check(instrList.isNotEmpty())
                        blockCmds[thisId] = instrList
                    }
                }
            }
        }

        fun tagNext(v: String) {
            this.checkNotFinished()
            if(pendingTag != null) {
                throw IllegalStateException("Already have pending tag $pendingTag")
            }
            pendingTag = v
        }

        private fun checkNotFinished() {
            if(finished) {
                throw IllegalStateException("Finished on this block, what have you done?")
            }
        }

        fun jump() {
            val current = thisId
            this.pushCommand(TACCmd.Simple.NopCmd)
            val next = idAlloc.freshBlock()
            blockGraph[current] = treapSetOf(next)
            this.flushBlock(next)
        }

        fun `while`(v: BuilderVar, cond: String, body: StmtBuilderScope.() -> Unit) {
            val loopHead = idAlloc.freshBlock()
            this.goto(loopHead)
            check(thisId == loopHead)
            val loopSuccessor = idAlloc.freshBlock()
            val loopBody = idAlloc.freshBlock()
            // we are now in the loop head
            v `=` cond
            this.pushCommand(TACCmd.Simple.JumpiCmd(
                    elseDst = loopSuccessor,
                    dst = loopBody,
                    cond = v.v,
                    meta = MetaMap()
            ))
            this.blockGraph[loopHead] = treapSetOf(loopSuccessor, loopBody)
            check(this.state == BlockState.Current)
            this.flushBlock(loopSuccessor)
            check(thisId == loopSuccessor)
            check(this.state == BlockState.Empty)
            val builder = StmtBuilderScope(
                    blockGraph, blockCmds, loopBody, idAlloc, BlockState.Empty
            )
            builder.body()
            val loopBodySuccs = mutableSetOf<NBId>()
            builder.finish(loopBodySuccs)
            loopBodySuccs.forEach {
                wireSuccessors(it, target = loopHead)
            }
            // force the loop body to have a successor
            this.pushCommand(TACCmd.Simple.NopCmd)
            this.checkInvariant()
        }

        private fun goto(tgt: NBId) {
            this.pushCommand(TACCmd.Simple.JumpCmd(
                    dst = tgt
            ))
            /*
               now in state 3
             */
            assert(thisId !in blockGraph)
            blockGraph[thisId] = treapSetOf(tgt)
            this.flushBlock(tgt)
            /*
              now in state Empty, no pending, no commands
             */
        }

        fun `return`(v: BuilderVar, len: Int) {
            this.pushCommand(
                    TACCmd.Simple.ReturnCmd(
                            memBaseMap = TACKeyword.MEMORY.toVar(),
                            o1 = v.v,
                            o2 = TACSymbol.lift(len)
                    )
            )
            blockGraph[thisId] = treapSetOf()
            state = BlockState.Exit
        }

        fun exit() {
            this.pushCommand(
                    TACCmd.Simple.RevertCmd(
                            base = TACKeyword.MEMORY.toVar(),
                            o1 = TACSymbol.lift(0),
                            o2 = TACSymbol.lift(0),
                            revertType = TACRevertType.BENIGN,
                            meta = MetaMap()
                    )
            )
            blockGraph[thisId] = treapSetOf()
            state = BlockState.Exit
        }

        fun assume(v: BuilderVar) {
            this.pushCommand(
                TACCmd.Simple.AssumeCmd(v.v)
            )
        }

        fun assert(v: BuilderVar, msg: String) {
            this.pushCommand(
                TACCmd.Simple.AssertCmd(v.v, msg)
            )
        }
    }

    data class MemRef(val base: TACSymbol.Var, val v: TACSymbol)
    data class StorageRef(val base: TACSymbol.Var, val v: TACSymbol.Var)

    fun make(f: StmtBuilderScope.() -> Unit) : TACCommandGraph {
        val allocer = NBIdAlloc()
        val blocks = MutableBlockGraph()
        val code = mutableMapOf<NBId, List<TACCmd.Simple>>()
        val builder = StmtBuilderScope(
                blockCmds = code,
                blockGraph = blocks,
                idAlloc = allocer,
                thisId = allocer.freshBlock(),
                state = BlockState.Empty
        )
        builder.f()
        val pending = mutableSetOf<NBId>()
        builder.finish(pending)
        for(p in pending) {
            if(code[p]?.isNotEmpty() == true) {
                blocks[p] = treapSetOf()
            }
        }
        return TACCommandGraph(blocks, code, TACSymbolTable.empty(), name = "test")
    }
}
