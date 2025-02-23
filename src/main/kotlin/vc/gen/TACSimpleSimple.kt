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

package vc.gen

import analysis.CmdPointer
import analysis.LTACCmd
import analysis.LTACCmdView
import analysis.maybeNarrow
import analysis.opt.inliner.InliningCalculator
import datastructures.stdcollections.*
import tac.Tag
import utils.*
import vc.data.*
import vc.data.TACMeta.ACCESS_PATHS
import vc.data.tacexprutil.DefaultTACExprTransformer
import vc.data.tacexprutil.TACUnboundedHashingUtils
import java.math.BigInteger
import java.util.concurrent.ConcurrentHashMap
import java.util.stream.Collectors

object TACSimpleSimple {

    fun TACCmd.Simple.inSimpleSimpleFragment() = this is TACCmd.Simple.AssigningCmd.AssignHavocCmd ||
        this is TACCmd.Simple.AssigningCmd.AssignExpCmd || this is TACCmd.Simple.AssumeCmd ||
        this is TACCmd.Simple.AssumeNotCmd || this is TACCmd.Simple.AssumeExpCmd ||
        this is TACCmd.Simple.AssertCmd || this is TACCmd.Simple.LabelCmd ||
        this is TACCmd.Simple.AnnotationCmd || this is TACCmd.Simple.JumpCmd || this is TACCmd.Simple.JumpiCmd ||
        this === TACCmd.Simple.NopCmd

    fun simpleSimpleHashing(p: CoreTACProgram): CoreTACProgram {
        val patching = p.toPatchingProgram()
        val inliningCalculator by lazy { InliningCalculator(p).also { it.go() } }
        patching.forEachOriginal { cmdPointer, simple ->
            when (simple) {
                is TACCmd.Simple.AssigningCmd.AssignSha3Cmd -> {
                    simpleSimplifyAssignSha3Cmd(simple, cmdPointer, patching, inliningCalculator)
                }

                else -> {}
            }
        }
        return patching.toCode(p, TACCmd.Simple.NopCmd)
    }

    private fun simpleSimplifyByteLongCopy(c: TACCmd.Simple.ByteLongCopy,   cmdPointer: CmdPointer,
                                           patching: SimplePatchingProgram,
                                           renamedDstmap: TACSymbol.Var) {
        patching.replaceCommand(
            cmdPointer, listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = c.dstBase,
                    rhs = TACExpr.LongStore(
                        dstMap = renamedDstmap.asSym(),
                        dstOffset = c.dstOffset.asSym(),
                        length = c.length.asSym(),
                        srcMap = c.srcBase.asSym(),
                        srcOffset = c.srcOffset.asSym()
                    ),
                    meta = c.meta
                )
            )
        )
    }

    private fun simpleSimplifyAssignSha3Cmd(
        c: TACCmd.Simple.AssigningCmd.AssignSha3Cmd,
        cmdPointer: CmdPointer,
        patching: SimplePatchingProgram,
        inliningCalculator: InliningCalculator, // passing this for optimizations
    ) {
        val (leadingConstants, computedLength) =
            TACUnboundedHashingUtils.HashOptimizer.getLeadingConstantsAndLength(
                LTACCmdView(LTACCmd(cmdPointer, c)),
                inliningCalculator
            )
        val (hashExp, newDecls, newCmds) = TACUnboundedHashingUtils.fromByteMapRange(
            hashFamily = HashFamily.Keccack, // TOOD: double check -- this one's really Keccack, the SimpleSha3 is actually Sha3 -- is that right, shelly? (should prob rename..)
            map = (c.memBaseMap as? TACSymbol.Var)
                ?: throw UnsupportedOperationException("Cannot convert constant hash base $c @ $cmdPointer"),
            start = c.op1.asSym(),
            length = c.op2.asSym(),
            leadingConstants = leadingConstants,
            computedLength = computedLength,
        )
        patching.addVarDecls(newDecls)
        patching.replaceCommand(
            cmdPointer,
            newCmds + TACCmd.Simple.AssigningCmd.AssignExpCmd(
                c.lhs,
                hashExp,
                c.meta
            )
        )
    }

    fun longCopySimple(p: CoreTACProgram): CoreTACProgram {
        /** simple-simple bytelongcopies.
         * these are problematic because they are converted to dstmap = longstore(dstmap, ...)
         * which means that if we now default-initialize dstmap (if it has no former definition),
         * then it'll have two definitions for the same incarnation, which will render dsa protection ineffective.
         * (so for that reason calldatabufs may lose their original name and callindex.)
         * the solution is to simplify the longcopy with an undefined dstmap and renaming that dstmap
         */

        val toHavoc = ConcurrentHashMap<TACSymbol.Var, TACSymbol.Var>()

        fun getHavocBase(it: CmdPointer, v: TACExpr.Sym.Var) : TACSymbol.Var? {
            if(v.s.tag != Tag.ByteMap) {
                return null
            }
            if(p.analysisCache.def.defSitesOf(v.s, it).isNotEmpty()) {
                return null
            }
            return toHavoc.computeIfAbsent(v.s) {
                it.toUnique("havocme").withMeta(TACMeta.TACSIMPLESIMPLE_HAVOCME).withoutMeta(TACMeta.CVL_DATA_OF)
            }
        }

        class ExpressionRewriter(
            private val where: CmdPointer
        ) : DefaultTACExprTransformer() {
            private var didSubstitution = false
            private var alreadyRan = false

            fun rewrite(e: TACExpr) : TACExpr? {
                require(!alreadyRan) {
                    "Cannot reuse expression rewriter"
                }
                alreadyRan = true
                return this.transform(e).takeIf {
                    didSubstitution
                }
            }

            override fun transformSelect(base: TACExpr, loc: TACExpr, tag: Tag?): TACExpr {
                if(base !is TACExpr.Sym.Var) {
                    return super.transformSelect(base, loc, tag)
                }
                val replaced = getHavocBase(where, base) ?: return super.transformSelect(base, loc, tag)
                didSubstitution = true
                return TACExpr.Select(
                    base = replaced.asSym(),
                    loc = super.transform(loc),
                    tag = tag
                )
            }

            // xxx why we don't just call this instead of implementing transformSelect and friends?
            override fun transformVar(exp: TACExpr.Sym.Var): TACExpr {
                return getHavocBase(where, exp)?.asSym()?.also { didSubstitution = true } ?: super.transformVar(exp)
            }

            override fun transformLongStore(
                dstMap: TACExpr,
                dstOffset: TACExpr,
                srcMap: TACExpr,
                srcOffset: TACExpr,
                length: TACExpr,
                tag: Tag?
            ): TACExpr {
                if(dstMap !is TACExpr.Sym.Var) {
                    return super.transformLongStore(dstMap, dstOffset, srcMap, srcOffset, length, tag)
                }
                val replaced = getHavocBase(where, dstMap) ?: return super.transformLongStore(dstMap, dstOffset, srcMap, srcOffset, length, tag)
                val srcMapReplacement = (srcMap as? TACExpr.Sym.Var)?.let { getHavocBase(where, it)?.asSym() } ?: super.transform(srcMap)
                didSubstitution = true
                return TACExpr.LongStore(
                    dstMap = replaced.asSym(),
                    dstOffset = super.transform(dstOffset),
                    srcMap = srcMapReplacement,
                    srcOffset = super.transform(srcOffset),
                    length = super.transform(length),
                    tag = tag
                )
            }

            override fun transformStore(base: TACExpr, loc: TACExpr, value: TACExpr, tag: Tag?): TACExpr {
                if(base !is TACExpr.Sym.Var) {
                    return super.transformStore(base, loc, value, tag)
                }
                val replaced = getHavocBase(where, base) ?: return super.transformStore(base, loc, value, tag)
                didSubstitution = true
                return TACExpr.Store(
                    base = replaced.asSym(),
                    loc = super.transform(loc),
                    value = super.transform(value),
                    tag = tag
                )
            }
        }

        return p.parallelLtacStream().mapNotNull { lcmd ->
            lcmd.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.let { assignExp ->
                val rhs = assignExp.cmd.rhs
                assignExp `to?` ExpressionRewriter(assignExp.ptr).rewrite(rhs)
            }
        }.sequential().collect(Collectors.toList()).let { toReplace ->
            p.patching { patch ->
                patch.addVarDecls(toHavoc.values.toSet())
                for((k,newRhs) in toReplace) {
                    patch.replaceCommand(k.ptr, listOf(k.cmd.copy(rhs = newRhs)))
                }
            }
        }
    }

    fun toSimpleSimple(p: CoreTACProgram): CoreTACProgram {
        val patching = p.toPatchingProgram()
        val inliningCalculator by lazy { InliningCalculator(p).also { it.go() } }
        patching.forEachOriginal { cmdPointer, simple ->
            when (simple) {
                is TACCmd.Simple.AssigningCmd.AssignExpCmd -> return@forEachOriginal
                is TACCmd.Simple.AssigningCmd.AssignSha3Cmd -> {
                    simpleSimplifyAssignSha3Cmd(simple, cmdPointer, patching, inliningCalculator)
                }

                is TACCmd.Simple.AssigningCmd.AssignSimpleSha3Cmd -> {
                    patching.replaceCommand(cmdPointer, listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            simple.lhs,
                            TACExpr.SimpleHash(
                                simple.length.asSym(),
                                simple.args.map { it.asSym() },
                                hashFamily = HashFamily.Keccack,
                            ),
                            simple.meta
                        )
                    ))
                }

                is TACCmd.Simple.AssigningCmd.ByteLoad -> {
                    patching.replaceCommand(
                        cmdPointer, listOf(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = simple.lhs,
                                rhs = TACExpr.Select(
                                    base = simple.base.asSym(),
                                    loc = simple.loc.asSym()
                                ),
                                meta = simple.meta
                            )
                        )
                    )
                }

                is TACCmd.Simple.AssigningCmd.ByteStore -> {
                    patching.replaceCommand(
                        cmdPointer, listOf(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = simple.base,
                                rhs = TACExpr.Store(
                                    base = simple.base.asSym(),
                                    loc = simple.loc.asSym(),
                                    value = simple.value.asSym()
                                ),
                                meta = simple.meta
                            )
                        )
                    )
                }

                is TACCmd.Simple.AssigningCmd.ByteStoreSingle -> {
                    val loc = simple.loc.asSym()
                    val value = simple.value.asSym()
                    val mod = TACExpr.BinOp.Mod(loc, 32.toBigInteger().asTACSymbol().asSym())
                    val alignedLoc = TACExpr.BinOp.Sub(
                        loc,
                        mod
                    )
                    val shiftFactor = TACExpr.Vec.Mul(
                        listOf(
                            BigInteger.valueOf(8).asTACSymbol().asSym(),
                            TACExpr.BinOp.Sub(
                                BigInteger.valueOf(31).asTACSymbol().asSym(),
                                mod
                            )
                        )
                    )
                    val oldValue = TACExpr.Select(simple.base.asSym(), alignedLoc)
                    val oldValueWithHole = TACExpr.BinOp.BWAnd(
                        oldValue,
                        TACExpr.UnaryExp.BWNot(
                            TACExpr.BinOp.ShiftLeft(
                                255.toBigInteger().asTACSymbol().asSym(),
                                shiftFactor
                            )
                        )
                    )
                    val rhsShifted = TACExpr.BinOp.ShiftLeft(
                        TACExpr.BinOp.BWAnd(
                            value, 255.toBigInteger().asTACSymbol().asSym()
                        ), shiftFactor
                    )
                    val newValue = TACExpr.BinOp.BWOr(oldValueWithHole, rhsShifted)
                    patching.replaceCommand(
                        cmdPointer, listOf(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = simple.base,
                                rhs = TACExpr.Store(
                                    base = simple.base.asSym(),
                                    loc = alignedLoc,
                                    value = newValue
                                ),
                                meta = simple.meta
                            )
                        )
                    )
                }

                is TACCmd.Simple.AssigningCmd.WordLoad -> {
                    val rhs = TACExpr.Select(
                        base = simple.base.asSym(),
                        loc = simple.loc.asSym()
                    ).let {
                        (it.loc as? TACExpr.Sym.Var)?.s?.meta?.get(ACCESS_PATHS)?.let { paths ->
                            TACExpr.AnnotationExp(it, ACCESS_PATHS, paths)
                        } ?: it
                    }
                    patching.update(cmdPointer,
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = simple.lhs,
                                rhs = rhs,
                                meta = simple.meta
                        )
                    )
                }

                is TACCmd.Simple.AssigningCmd.AssignMsizeCmd -> {
                    patching.replaceCommand(
                        cmdPointer, listOf(
                            TACCmd.Simple.AssigningCmd.AssignHavocCmd(
                                lhs = simple.lhs,
                                meta = simple.meta
                            )
                        )
                    )
                }

                is TACCmd.Simple.AssigningCmd.AssignGasCmd -> {
                    patching.replaceCommand(
                        cmdPointer, listOf(
                            TACCmd.Simple.AssigningCmd.AssignHavocCmd(
                                lhs = simple.lhs,
                                meta = simple.meta
                            )
                        )
                    )
                }

                is TACCmd.Simple.AssigningCmd.AssignHavocCmd -> return@forEachOriginal
                is TACCmd.Simple.AnnotationCmd,
                is TACCmd.Simple.LabelCmd -> return@forEachOriginal

                is TACCmd.Simple.WordStore -> {
                    val rhs = TACExpr.Store(
                        value = simple.value.asSym(),
                        base = simple.base.asSym(),
                        loc = simple.loc.asSym()
                    ).let {
                        (it.loc as? TACExpr.Sym.Var)?.s?.meta?.get(ACCESS_PATHS)?.let { paths ->
                            TACExpr.AnnotationExp(it, ACCESS_PATHS, paths)
                        } ?: it
                    }
                    patching.replaceCommand(
                        cmdPointer, listOf(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = simple.base,
                                rhs = rhs,
                                meta = simple.meta
                            )
                        )
                    )
                }

                is TACCmd.Simple.ByteLongCopy -> {
                    simpleSimplifyByteLongCopy(simple, cmdPointer, patching, simple.dstBase)
                }

                is TACCmd.Simple.JumpCmd,
                is TACCmd.Simple.JumpiCmd -> return@forEachOriginal

                is TACCmd.Simple.SummaryCmd -> throw UnsupportedOperationException("Summary command $simple @ $cmdPointer falls outside fragment")
                is TACCmd.Simple.CallCore -> throw UnsupportedOperationException("Call core $simple @ $cmdPointer should have been replaced")
                is TACCmd.Simple.JumpdestCmd,
                is TACCmd.Simple.LogCmd,
                is TACCmd.Simple.ReturnCmd,
                is TACCmd.Simple.ReturnSymCmd,
                is TACCmd.Simple.RevertCmd -> patching.replaceCommand(cmdPointer, listOf(), null)

                TACCmd.Simple.NopCmd -> patching.replaceCommand(cmdPointer, listOf(), null)
                is TACCmd.Simple.AssumeCmd,
                is TACCmd.Simple.AssumeNotCmd,
                is TACCmd.Simple.AssumeExpCmd,
                is TACCmd.Simple.AssertCmd -> return@forEachOriginal
            }
        }
        return patching.toCode(p, TACCmd.Simple.NopCmd)
    }
}
