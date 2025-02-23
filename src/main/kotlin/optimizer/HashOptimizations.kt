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

package optimizer

import analysis.CmdPointer
import analysis.LTACCmd
import analysis.NonTrivialDefAnalysis
import analysis.hash.DisciplinedHashModel
import analysis.icfg.ExpressionSimplifier
import analysis.narrow
import compiler.applyKeccak
import config.Config
import evm.EVM_WORD_SIZE
import evm.EVM_WORD_SIZE_INT
import log.Logger
import log.LoggerTypes
import scene.IScene
import scene.ITACMethod
import scene.MethodAttribute
import tac.MetaMap
import utils.*
import vc.data.*
import verifier.SimpleMemoryOptimizer
import java.math.BigInteger

private val logger = Logger(LoggerTypes.OPTIMIZE)

/**
 * 1. Converting raw hash (keccak256) calls to simplified ones (i.e. storage access)
 * 2. Concretizing constant string hashes
 */
fun hashRewrites(scene: IScene, m: ITACMethod): CoreTACProgram {
    val c = m.code as CoreTACProgram

    val mapper = object: TACCmdMapperWithPointer {
        override val decls: MutableSet<TACSymbol.Var> = mutableSetOf()


        val graph = c.analysisCache.graph
        val exprSimplifier = ExpressionSimplifier(graph, graph.cache.def)

        // simplifying keccak calls with offset 0 and size 64
        fun mapAssignKeccackCmd(
            lhs: TACSymbol.Var,
            op1: TACSymbol,
            op2: TACSymbol,
            memBaseMap: TACSymbol.Var,
            metaMap: MetaMap
        ): List<TACCmd.Simple> {
            inv()
            val default = TACCmd.Simple.AssigningCmd.AssignSha3Cmd(lhs, op1, op2, memBaseMap, metaMap)
            val offsetArg = exprSimplifier.simplify(op1, currentPtr!!, true).getAsConst()
            val offsetArgIs0 = offsetArg == BigInteger.ZERO
            val sizeArg = exprSimplifier.simplify(op2, currentPtr!!, true).getAsConst()
            val sizeArgIs64 = sizeArg == BigInteger.valueOf(64)
            val sizeArgIs32 = sizeArg == BigInteger.valueOf(32)
            return listOf(
                if (offsetArgIs0 && sizeArgIs64) {
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs,
                        TACExpr.SimpleHash(
                            (EVM_WORD_SIZE_INT * 2).asTACExpr,
                            listOf(
                                TACExpr.Select(memBaseMap.asSym(), BigInteger.ZERO.asTACSymbol().asSym()),
                                TACExpr.Select(memBaseMap.asSym(), BigInteger.valueOf(32).asTACSymbol().asSym())
                            ),
                            hashFamily = HashFamily.Keccack
                        )
                    )
                } else if (offsetArgIs0 && sizeArgIs32) {
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs,
                        TACExpr.SimpleHash(
                            EVM_WORD_SIZE.asTACExpr,
                            listOf(
                                TACExpr.Select(memBaseMap.asSym(), BigInteger.ZERO.asTACSymbol().asSym())
                            ),
                            HashFamily.Keccack
                        )
                    )
                } else if (sizeArg != null) {
                    // trace back a Bytelongcopy
                    val currentPtrInst = currentPtr!!
                    val codedataCopy = graph
                        .iterateUntil(currentPtrInst)
                        .lastOrNull { ltacCmd ->
                            // find the last:
                            ltacCmd.cmd is TACCmd.Simple.ByteLongCopy && // bytelongcopy
                            ltacCmd.cmd.srcBase.meta.contains(TACMeta.CODEDATA_KEY) && // from codedata
                            NonTrivialDefAnalysis(graph).let { ntda -> // whose dstOffset agrees with hash start offset
                                op1 is TACSymbol.Var &&
                                ntda.nontrivialDef(
                                    op1,
                                    currentPtrInst
                                ) == ntda.nontrivialDef(ltacCmd.cmd.dstOffset as TACSymbol.Var, ltacCmd.ptr)
                            } &&
                            exprSimplifier.simplify(ltacCmd.cmd.length, ltacCmd.ptr, true) // and length agrees with the const size
                                .getAsConst() == sizeArg
                            // ME analysis not working here because the length of the hash is a subtraction
                            // op2 in c.analysisCache.me.equivBefore(ltacCmd.ptr, ltacCmd.cmd.length as TACSymbol.Var)
                        }
                    val bytesAndHash = codedataCopy?.narrow<TACCmd.Simple.ByteLongCopy>()
                        ?.let { blc ->
                            val bytecode = extractBytecode(scene, m)
                            resolveByteLongCopyFromCodedata(blc.cmd.srcOffset, blc.cmd.length, blc.ptr, exprSimplifier, bytecode)
                        }
                    if (bytesAndHash != null) {
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(lhs, bytesAndHash.second.asTACSymbol())
                    } else {
                        default
                    }
                } else {
                    default
                }
            )
        }

        /**
         * Replace x = keccak256simple(len, offsets, sym1, ..., symn)
         * WHEN:
         * - all arguments are constant
         * - len >= Config.EvaluateLiteralHashLength
         * WITH:
         *   the actual value of keccak256(len, offsets, sym1, ..., symn)
         */
        fun mapAssignSimpleSha3Cmd(
            lhs: TACSymbol.Var,
            len: TACSymbol.Const,
            args: List<TACSymbol>,
            meta: MetaMap,
            ptr: CmdPointer,
        ): List<TACCmd.Simple> {
            val default = listOf(
                TACCmd.Simple.AssigningCmd.AssignSimpleSha3Cmd(lhs, len, args, meta)
            )
            /**
             * Only those hashes we are *reasonably* certain are not part of storage slot
             * computation will have this meta. If it is missing, conservatively bail out, we don't
             * want to eagerly evaluate constant map keys or array locations.
             */
            if(TACMeta.DECOMPOSED_USER_HASH !in meta) {
                return default
            }

            val evaluatedArguments = args.monadicMap {
                exprSimplifier.simplify(it, ptr, true).getAsConst()
            } ?: return default

            val size = len.value
            if (size < Config.EvaluateLiteralHashLength.get().toBigInteger()) {
                return default
            }
            val numberOfSymbols = (size / EVM_WORD_SIZE).intValueExact() + if(size.mod(EVM_WORD_SIZE) != BigInteger.ZERO) {
                1
            } else {
                0
            }
            val symbolsNotLength = (evaluatedArguments.size)
            if(symbolsNotLength != numberOfSymbols) {
                /*
                 did we opt in to offset tracking somehow? If this was a string constant, we would expect to not see
                 this, but perhaps the user turned on aggressive hash decomposition
                 */
                val offsets = DisciplinedHashModel.computeOffsetTaggingFor((0 until numberOfSymbols).map {
                    it.toBigInteger() * EVM_WORD_SIZE
                })
                if(offsets.size + numberOfSymbols != symbolsNotLength) {
                    return default
                }
                if(offsets.withIndex().any {(ind, expectedVal) ->
                    evaluatedArguments[ind] != expectedVal
                }) {
                    return default
                }
            }

            val hashResult = applyKeccak(*evaluatedArguments.toTypedArray())
            return listOf(TACCmd.Simple.AssigningCmd.AssignExpCmd(lhs, hashResult.asTACExpr))
        }

        override var currentPtr: CmdPointer? = null

        override fun mapCommand(c: LTACCmd): List<TACCmd.Simple> {
            return when (val cmd = c.cmd) {
                is TACCmd.Simple.AssigningCmd.AssignSha3Cmd -> mapAssignKeccackCmd(
                    cmd.lhs,
                    cmd.op1,
                    cmd.op2,
                    cmd.memBaseMap,
                    cmd.meta
                )
                is TACCmd.Simple.AssigningCmd.AssignSimpleSha3Cmd -> mapAssignSimpleSha3Cmd(
                    cmd.lhs,
                    cmd.length,
                    cmd.args,
                    cmd.meta,
                    c.ptr,
                )
                else -> listOf(cmd)
            }
        }
    }

    return mapper.mapCommands(c)
}

fun rewriteCodedataCopy(scene: IScene, m: ITACMethod): CoreTACProgram {
    val c = m.code as CoreTACProgram

    val mapper = object: TACCmdMapperWithPointer {
        override val decls: MutableSet<TACSymbol.Var> = mutableSetOf()

        val graph = c.analysisCache.graph
        val exprSimplifier = ExpressionSimplifier(graph, graph.cache.def)

        fun mapByteLongCopy(
            dstBase: TACSymbol.Var,
            dstOffset: TACSymbol,
            length: TACSymbol,
            srcBase: TACSymbol.Var,
            srcOffset: TACSymbol,
            metaMap: MetaMap
        ): List<TACCmd.Simple> {
            val default = TACCmd.Simple.ByteLongCopy(dstOffset, srcOffset, length, dstBase, srcBase, metaMap)
            if (srcBase.meta.contains(TACMeta.CODEDATA_KEY)) {
                val currentPtrInst = currentPtr!!
                val bytecode = extractBytecode(scene, m)
                val stringAndHash = resolveByteLongCopyFromCodedata(srcOffset, length, currentPtrInst, exprSimplifier, bytecode)
                if (stringAndHash != null) {
                    logger.info { "Resolved string $stringAndHash in $currentPtrInst" }
                    val res = SimpleMemoryOptimizer.rewriteByteLongCopyThatCopiesString(stringAndHash.first, default, currentPtr!!, exprSimplifier)
                    decls.addAll(res.varDecls)
                    return res.cmds
                }
            }
            return listOf(default)
        }

        override var currentPtr: CmdPointer? = null

        override fun mapCommand(c: LTACCmd): List<TACCmd.Simple> {
            return when (val cmd = c.cmd) {
                is TACCmd.Simple.ByteLongCopy -> mapByteLongCopy(
                    cmd.dstBase,
                    cmd.dstOffset,
                    cmd.length,
                    cmd.srcBase,
                    cmd.srcOffset,
                    cmd.meta
                )
                else -> listOf(cmd)
            }
        }

        // TODO CERT-6315: byteload from codedata should be converted too!
    }

    return mapper.mapCommands(c)
}

// given [scene], and CoreTACProgram [c] from the scene, and the expected [contractAddress],
// returns the bytecode associated with the contract, either runtime or constructor
// (depending whether we came from constructor instance or a regular method)
private fun extractBytecode(scene: IScene, m: ITACMethod): List<UByte> {
    val contract = scene.getContract(m.getContainingContract().instanceId)
    val bytecode = if (m.attribute == MethodAttribute.Unique.Constructor) {
        contract.constructorBytecode!!.bytes
    } else {
        contract.bytecode!!.bytes
    }
    return bytecode
}

private fun resolveByteLongCopyFromCodedata(
    srcOffset: TACSymbol,
    length: TACSymbol,
    ptr: CmdPointer,
    exprSimplifier: ExpressionSimplifier,
    bytecode: List<UByte>
): Pair<String, BigInteger>? {
    val offset = exprSimplifier.simplify(srcOffset, ptr, true).getAsConst()
    val sz = exprSimplifier.simplify(length, ptr, true).getAsConst()
    if (offset != null && sz != null) {
        return resolveBytecodeRange(bytecode,offset,sz)
    }
    return null
}

fun resolveBytecodeRange(bytecode: List<UByte>, offset: BigInteger, sz: BigInteger): Pair<String, BigInteger>? {
    val startInBytecode = offset.intValueExact()
    val lengthInBytecode = sz.intValueExact()
    if (startInBytecode + lengthInBytecode <= bytecode.size) {
        val bytes = bytecode.subList(startInBytecode, startInBytecode + lengthInBytecode)
        return bytes.map {
            @Suppress("DEPRECATION") // CER-1486
            it.toInt().toChar()
        }.joinToString("") to
            applyKeccak(bytes)
    }
    return null
}
