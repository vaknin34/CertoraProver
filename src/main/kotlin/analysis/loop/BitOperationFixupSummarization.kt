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

import analysis.*
import analysis.smtblaster.*
import parallel.Parallel
import parallel.Scheduler.complete
import parallel.Scheduler.rpc
import parallel.bindFalseAsNull
import smtlibutils.data.SmtExp
import statistics.*
import tac.Tag
import utils.*
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACKeyword
import vc.data.TACSymbol
import vc.data.tacexprutil.TACExprTransformer
import datastructures.stdcollections.*

private const val readName = "READ-VALUE"

private const val preserveConstName = "PRESERVE-AMOUNT"

private const val expectedConstName = "EXPECTED"
private const val clearAmountName = "CLEAR-AMOUNT"

private const val lowerMaskName = "LOWER-MASK"

private const val preserveMaskConstName = "PRESERVE-MASK"

class BitOperationFixupSummarization(
        blaster: IBlaster,
        graph: TACCommandGraph
) : CommonBranchingFixupReasoning(blaster, me = graph.cache.gvn, builder = SmtExpBitVectorTermBuilder) {

    private val expressionTranslator = ExpressionTranslator(
            builder,
            toTypedArray = List<SmtExp>::toTypedArray
    )

    private val gvn by lazy {
        graph.cache.gvn
    }

    private val check by lazy {
        val indexPattern = PatternDSL.build {
            (Var - Var).withAction { w, _, sub ->
                w to sub
            }
        }
        val overflowCalc = PatternDSL.build {
            (PatternMatcher.Pattern.FromBinOp.from(
                    TACExpr.BinOp.Exponent::class.java,
                    p1 = PatternMatcher.Pattern.FromConstant.exactly(256.toBigInteger()),
                    p2 = PatternDSL.build {
                        (32() - Var).locSecond
                    },
                    comb = { _, _, w ->
                        w
                    }
            ).asBuildable() - 1()).first
        }
        val presrveMask = PatternMatcher.Pattern.AssigningPattern1(
                extract = { _: LTACCmd, l: TACCmd.Simple.AssigningCmd ->
                    (((l as? TACCmd.Simple.AssigningCmd.AssignExpCmd)?.rhs as? TACExpr.UnaryExp.BWNot)?.o as? TACExpr.Sym)?.s
                },
                nested = overflowCalc,
                out = { _, l -> l }
        )

        val origValue = PatternMatcher.Pattern.AssigningPattern1(extract = { _, l: TACCmd.Simple.AssigningCmd ->
            (l as? TACCmd.Simple.AssigningCmd.ByteLoad)?.takeIf {
                it.base == TACKeyword.MEMORY.toVar() && it.loc is TACSymbol.Var
            }?.loc
        },
                nested = indexPattern, out = { w, l ->
            w.narrow<TACCmd.Simple.AssigningCmd.ByteLoad>() to l
        })

        val bitwiseAnd = PatternDSL.build {
            (presrveMask.asBuildable() and origValue.asBuildable()).withAction { _, subAmount, readValue ->
                subAmount to readValue
            }
        }
        PatternMatcher.compilePattern(graph = graph, patt = bitwiseAnd)
    }

    override fun checkFixupBlock(
        scriptGen: Generator,
        destBlock: TACBlock,
        localState: MutableMap<TACSymbol.Var, TACExpr>,
        localMapper: TACExprTransformer<TACExpr>
    ): Parallel<FixupBlockResult?> {
        val sliced = destBlock.commands.takeWhile {
            it.cmd !is TACCmd.Simple.AssigningCmd.ByteStore
        }
        if(sliced.size == destBlock.commands.size) {
            return complete(null)
        }
        val finalWrite  = destBlock.commands[sliced.size].narrow<TACCmd.Simple.AssigningCmd.ByteStore>()
        // short-circuit I guess
        val finalWriteIdx = finalWrite.cmd.loc as? TACSymbol.Var
        val finalWriteValue = finalWrite.cmd.value as? TACSymbol.Var
        if(finalWriteIdx != null && finalWriteValue != null) {
            check.query(finalWriteValue, finalWrite.wrapped).toNullableResult()?.takeIf { (subAmount, readValue) ->
                // read and write from the same index
                readValue.first.cmd.loc in gvn.findCopiesAt(readValue.first.ptr, finalWrite.ptr to finalWriteIdx) &&
                        // subtraction amounts are the same
                    subAmount.second in gvn.findCopiesAt(subAmount.first.ptr, readValue.second.first.ptr to readValue.second.second)
            }?.let {(_, readValue) ->
                return complete(FixupBlockResult(
                    fixupEnd = finalWrite.ptr,
                    outputAccess = setOf(readValue.first.ptr, finalWrite.ptr),
                    inputAccess = setOf()
                ))
            }
        }
        var seenRead = false
        var readLoc : CmdPointer? = null
        var readIdx: TACExpr? = null
        val toDeclare = mutableSetOf<String>()
        for(lc in sliced) {
            if(lc.cmd is TACCmd.Simple.AssigningCmd.ByteLoad) {
                if(seenRead) {
                    return complete(null)
                }
                seenRead = true
                readLoc = lc.ptr
                if(lc.cmd.base != TACKeyword.MEMORY.toVar() || lc.cmd.loc !is TACSymbol.Var) {
                    return complete(null)
                }
                readIdx = localState[lc.cmd.loc] ?: return complete(null)
                val ind = readIdx.let {
                    expressionTranslator.blastExpr(it) {
                        it.toSMTRep()
                    }
                } ?: return complete(null)
                if(!scriptGen.bind { fork ->
                        fork.assert {
                            ge(
                                minus(
                                    toIdent(LoopRole.END.name),
                                    ind
                                ),
                                const(32)
                            )
                        }
                        fork.checkSat()
                    }.build().let { fork ->
                        this@BitOperationFixupSummarization.zBlaster.blastSmt(fork.cmdList)
                    }
                ) {
                    return complete(null)
                }
                toDeclare.add(readName)
                localState[lc.cmd.lhs] = TACSymbol.Var(
                        readName, tag = Tag.Bit256
                ).asSym()
            } else if(lc.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && lc.cmd.rhs is TACExpr.BinOp.Exponent) {
                if(lc.cmd.rhs.o1 == TACSymbol.lift(256).asSym()) {
                    localState[lc.cmd.lhs] = TACExpr.BinOp.ShiftLeft(
                            TACSymbol.lift(1).asSym(),
                            TACExpr.Vec.Mul(
                                    TACSymbol.lift(8).asSym(),
                                    localMapper.transform(lc.cmd.rhs.o2)
                            )
                    )
                } else {
                    return complete(null)
                }
            } else {
                if(!stepSymbolic(localMapper, localState, lc)) {
                    return complete(null)
                }
            }
        }
        val finalIdx = (finalWrite.cmd.loc as? TACSymbol.Var)?.let(localState::get) ?: return complete(null)
        if(!seenRead) {
            return complete(null)
        }
        // we're writing back at the same place we wrote. Are we guaranteed to preserve the remaining bits?
        if(!LogicalEquivalence.equiv(finalIdx, readIdx!!)) {
            return complete(null)
        }
        if(finalWrite.cmd.value !is TACSymbol.Var) {
            return complete(null)
        }
        val writeExpr = localState[finalWrite.cmd.value as TACSymbol.Var]?.let {
            expressionTranslator.blastExpr(it) { it.toSMTRep() }
        } ?: return complete(null)
        val script = scriptGen.bind { script ->
            for (decl in toDeclare) {
                script.declare(decl)
            }
            script.define(preserveConstName) {
                mult(
                    const(8), // 8 bits per byte
                    minus(
                        toIdent(LoopRole.END.name),
                        expressionTranslator.blastExpr(readIdx) { it.toSMTRep() }!!
                    )
                )
            }
            script.define(clearAmountName) {
                minus(const(256), toIdent(preserveConstName))
            }
            script.define(lowerMaskName) {
                minus(shl(const(1), script.toIdent(clearAmountName))!!, const(1))
            }
            script.define(preserveMaskConstName) {
                bwNot(toIdent(lowerMaskName))!!
            }
            script.define(expectedConstName) {
                bwAnd(toIdent(readName), toIdent(preserveMaskConstName))!!
            }
            script.assert {
                lnot(eq(toIdent(expectedConstName), writeExpr))
            }
            script.checkSat()
        }.build()
        return rpc {
            val x = ElapsedTimeStats("loop-fixup".toSDFeatureKey()).startMeasuringTimeOf("bitOpFixup".toTimeTag())

            this.zBlaster.blastSmt(script.cmdList).also {
                x.endMeasuringTimeOf("bitOpFixup".toTimeTag())
                SDCollectorFactory.collector().collectFeature(x)
            }
        }.bindFalseAsNull {
            complete(FixupBlockResult(
                fixupEnd = finalWrite.ptr,
                inputAccess = setOf(),
                outputAccess = setOf(finalWrite.ptr, readLoc!!)
            ))
        }
    }

    override fun plasusibleFixupBlock(b: TACBlock): Boolean {
        return super.plasusibleFixupBlock(b) && b.commands.takeWhile {
            it.cmd !is TACCmd.Simple.AssigningCmd.ByteStore
        }.any {
            it.cmd is TACCmd.Simple.AssigningCmd.ByteLoad
        }
    }
}
