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

package vc.data.minitac

import com.certora.collect.*
import datastructures.LinkedArrayHashMap
import datastructures.stdcollections.*
import kotlinx.serialization.DeserializationStrategy
import kotlinx.serialization.json.Json
import tac.BlockIdentifier
import tac.MetaKey
import tac.NBId
import tac.Tag
import vc.data.*
import vc.data.minitac.MiniTACCompiler.PluginHandler
import vc.data.tacexprutil.getFreeVars

typealias VariableGenerator = (String) -> TACSymbol.Var

class MiniTACCompiler private constructor(private val c: List<MiniTACCmd>, private val handlers: Map<String, PluginHandler>, @Suppress(
    "UNUSED_PARAMETER"
) dummy: Int?) {
    fun interface PluginHandler {
        /**
         * Invoked by the compiler when encountering an [MiniTACCmd.Opaque] embedding. [payload] is the raw string
         * found between the delimiters in the embed command, and [gen] is a helper class which generates
         * variables in the symbol table of the compiled program.
         *
         * These plugins should only produce straightline code.
         *
         * Finally, for automatic structure on the payloads, see [handler].
         */
        fun compile(payload: String, gen: VariableGenerator) : List<TACCmd.Simple>
    }

    companion object {
        /**
         * Compile the mini tac program [c] using the handlers in [handlers].
         */
        operator fun invoke(c: List<MiniTACCmd>, handlers: Map<String, PluginHandler>) : CoreTACProgram {
            return MiniTACCompiler(c, handlers, null).compile()
        }

        val MARKER = MetaKey<String>("mini.tac.marker")

        /**
         * Create a [PluginHandler] for the embed command with [key], which interprets the payload given in the command
         * as a json string seralized with [ser]. This deserialized representation is then passed to [cb] for translation
         * into a sequence of TAC commands.
         */
        fun <T> handler(key: String, ser: DeserializationStrategy<T>, cb: (T, VariableGenerator) -> List<TACCmd.Simple>) : Pair<String, PluginHandler> {
            return key to PluginHandler { payload, gen ->
                cb(Json.decodeFromString(ser, payload), gen)
            }
        }
    }

    private class BlockBuilder(val thisId: NBId) {
        var finished = false
        val cmds = mutableListOf<TACCmd.Simple>()
    }

    interface Continuation {
        val succBlock: NBId
        fun k()
    }

    val blockgraph = mutableMapOf<NBId, TreapSet<NBId>>()
    val code = mutableMapOf<NBId, List<TACCmd.Simple>>()

    private var blockCounter = 0

    private val seenTags = mutableMapOf<TACSymbol.Var, Tag>()

    private fun freshBlock(): NBId {
        return BlockIdentifier(calleeIdx = 0, origStartPc = blockCounter++, decompCopy = 0, freshCopy = 0, stkTop = 0, topOfStackValue = 0)
    }

    private val labelToBlock = mutableMapOf<String, NBId>()

    private fun BlockBuilder.finishWithSucc(vararg nxt: NBId) {
        if(finished) {
            throw IllegalStateException("Cannot finalize block twice")
        }
        code[this.thisId] = this.cmds.takeIf { it.isNotEmpty() } ?: listOf(TACCmd.Simple.NopCmd)
        blockgraph[this.thisId] = nxt.toSet().toTreapSet()
    }

    private fun getBlockForLabel(s: String) = labelToBlock.getOrPut(s) {
        freshBlock()
    }

    private fun newBlockBuilder(): BlockBuilder {
        return BlockBuilder(freshBlock())
    }



    private fun blockBuilderFrom(l: MiniTACCmd) : BlockBuilder {
        if(l is MiniTACCmd.LabelCmd) {
            return BlockBuilder(getBlockForLabel(l.label))
        } else {
            return BlockBuilder(freshBlock())
        }
    }

    private fun blockBuilderFrom(t: List<MiniTACCmd>, i: Int) = blockBuilderFrom(t[i])

    private fun getBlockContinuation(knownNext: NBId?): Continuation {
        if(knownNext == null) {
            val freshBlock =  freshBlock()
            code[freshBlock] = listOf(TACCmd.Simple.LabelCmd("Halt"))
            blockgraph[freshBlock] = treapSetOf()
            return object : Continuation {
                override val succBlock: NBId
                    get() = freshBlock
                override fun k() { }
            }
        } else {
            return object : Continuation {
                override val succBlock: NBId
                    get() = knownNext
                override fun k() { }

            }
        }
    }

    private fun getContinuation(
        it: Int,
        toCompile: List<MiniTACCmd>,
        knownNext: NBId?
    ) : Continuation {
        val isLast = it == toCompile.lastIndex
        return if(isLast) {
            getBlockContinuation(knownNext)
        } else {
            val nxtBuilder = blockBuilderFrom(toCompile, it + 1)
            object : Continuation {
                override val succBlock: NBId
                    get() = nxtBuilder.thisId

                override fun k() {
                    compileSequence(nxtBuilder, it + 1, toCompile, knownNext)
                }
            }
        }
    }

    private fun recordVariable(it: TACSymbol.Var) {
        val curr = seenTags[it]
        if(curr != null && curr != it.tag) {
            throw IllegalStateException("Cannot tag $it with $curr and ${it.tag}")
        }
        seenTags[it] = it.tag
    }

    private fun recordVariables(e: TACExpr) {
        e.getFreeVars().forEach {
            recordVariable(it)
        }
    }

    private fun compileConditional(block: BlockBuilder, e: TACExpr, trueBranch: NBId, falseBranch: NBId) {
        val compFlag = TACKeyword.TMP(Tag.Bool, "!cmp")
        recordVariable(compFlag)
        if(e is TACExpr.Unconstrained) {
            block.cmds.add(
                TACCmd.Simple.AssigningCmd.AssignHavocCmd(
                    lhs = compFlag
                ),
            )
        } else {
            val tmp = TACKeyword.TMP(Tag.Bit256, "!tmp")

            recordVariable(tmp)
            block.cmds.addAll(listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = tmp,
                    rhs = e
                ),
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = compFlag,
                    rhs = TACExpr.BinRel.Lt(TACExpr.zeroExpr, tmp.asSym())
                )
            ))
        }
        block.cmds.add(TACCmd.Simple.JumpiCmd(cond = compFlag, dst = trueBranch, elseDst = falseBranch))
        block.finishWithSucc(falseBranch, trueBranch)
    }

    private fun compileSequence(block: BlockBuilder, i: Int, toCompile: List<MiniTACCmd>, knownNext: NBId?) {

        var it = i
        while(it < toCompile.size) {
            val cmd = toCompile[it]
            if(cmd is MiniTACCmd.WithExpressionCommand) {
                recordVariables(cmd.expr)
            }
            when(cmd) {
                is MiniTACCmd.Assign -> {
                    block.cmds.add(TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = cmd.lhs,
                        rhs = cmd.rhs
                    ))
                    recordVariable(cmd.lhs)
                }
                is MiniTACCmd.Conditional -> {
                    val next = getContinuation(it, toCompile, knownNext)

                    val thenBranch = blockBuilderFrom(cmd.thenBranch, 0)
                    compileSequence(thenBranch, 0, cmd.thenBranch, next.succBlock)
                    val elseDest = if(cmd.elseBranch == null) {
                        next.succBlock
                    } else {
                        val elseBranch = blockBuilderFrom(cmd.elseBranch, 0)
                        compileSequence(elseBranch, 0, cmd.elseBranch, next.succBlock)
                        elseBranch.thisId
                    }
                    compileConditional(block, cmd.cond, trueBranch = thenBranch.thisId, falseBranch = elseDest)
                    return next.k()
                }
                is MiniTACCmd.GotoCmd -> {
                    val nxt = getBlockForLabel(cmd.label)
                    block.cmds.add(TACCmd.Simple.JumpCmd(nxt))
                    block.finishWithSucc(nxt)
                    return
                }
                is MiniTACCmd.LabelCmd -> {
                    if(block.thisId != getBlockForLabel(cmd.label)) {
                        val nxt = blockBuilderFrom(cmd)
                        block.finishWithSucc(nxt.thisId)
                        return compileSequence(nxt, it, toCompile, knownNext)
                    }
                }
                is MiniTACCmd.Marker -> block.cmds.add(TACCmd.Simple.AnnotationCmd(MARKER, cmd.payload))
                is MiniTACCmd.Opaque -> {
                    val h = handlers[cmd.handler] ?: throw IllegalStateException("no handler for ${cmd.handler}")
                    block.cmds.addAll(h.compile(cmd.payload) {
                        val toRet = TACSymbol.Var(it, Tag.Bit256)
                        recordVariable(toRet)
                        toRet
                    })
                }
                is MiniTACCmd.While -> {
                    val headerBody = newBlockBuilder()
                    block.finishWithSucc(headerBody.thisId)

                    val blockBody = blockBuilderFrom(cmd.body, 0)
                    val next = getContinuation(it, toCompile, knownNext)
                    compileConditional(headerBody, e = cmd.cond, trueBranch = blockBody.thisId, falseBranch = next.succBlock)
                    compileSequence(blockBody, 0, cmd.body, headerBody.thisId)

                    return next.k()
                }
            }
            it++
        }
        val c = getBlockContinuation(knownNext)
        block.finishWithSucc(c.succBlock)
        c.k()
    }

    fun compile() : CoreTACProgram {
        val rootBlock = blockBuilderFrom(c, 0)
        compileSequence(rootBlock, 0, c, null)
        return CoreTACProgram(blockgraph = LinkedArrayHashMap(blockgraph), code = code, check = true, procedures = setOf(), name = "auto-gen", instrumentationTAC = InstrumentationTAC(UfAxioms.empty()), symbolTable = TACSymbolTable(seenTags.keys))
    }
}

