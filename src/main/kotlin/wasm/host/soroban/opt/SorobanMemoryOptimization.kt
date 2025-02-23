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

package wasm.host.soroban.opt

import analysis.*
import analysis.CommandWithRequiredDecls.Companion.mergeMany
import analysis.icfg.*
import config.*
import datastructures.stdcollections.*
import instrumentation.transformers.*
import kotlin.streams.*
import log.*
import optimizer.*
import report.*
import tac.*
import utils.*
import vc.data.*
import vc.data.TACExprFactUntyped as expr
import vc.data.tacexprutil.*
import verifier.*
import wasm.impCfg.WasmImpCfgToTAC.MEMORY_INITIALIZATION
import wasm.tacutils.*
import java.util.concurrent.*

private val logger = Logger(LoggerTypes.WASM)

val LONG_COPY_STRIDE = MetaKey<Int>("wasm.soroban.long.copy.stride")

/**
    Scalarizes memory accesses in the Soroban program.

    Soroban programs typically do not have a dynamic memory allocator.  Nor do they typically use mutable pointers.
    Dynamic data structures are typically maintained by the host environment.  The only mutable pointer value we are
    likely to encounter is the stack pointer, whose value at any given point in the inlined, unrolled program is static.

    Given this observation, we expect to be able to determine the locations of all memory accesses statically, and thus
    we can scalarize all memory accesses, making later optimizations much more effective.
 */
fun optimizeSorobanMemory(code: CoreTACProgram): CoreTACProgram {

    // We assume this runs after constant propagation, so ExpressionSimplifier should be able to find constant values
    // reasonably quickly.
    val simplifier = ExpressionSimplifier(code.analysisCache.graph, trySimplifyConfluence = true)

    val scalars = ConcurrentHashMap<UInt, TACSymbol.Var>()
    fun UInt.toScalar() = scalars.computeIfAbsent(this) {
        TACSymbol.Var("mem0x${it.toString(16)}", Tag.Bit256)
    }

    val failures = ConcurrentLinkedDeque<LTACCmd>()

    val replacements = code.parallelLtacStream().mapNotNull { lcmd ->
        val (ptr, cmd) = lcmd

        fun <T> fail(): T? {
            failures += lcmd
            return null
        }

        fun TACExpr.tryToBigInteger() = simplifier.simplify(this, ptr, true).getAsConst() ?: fail()

        fun TACExpr.tryToUInt() = tryToBigInteger()?.toUIntOrNull() ?: fail()
        fun TACSymbol.tryToUInt() = this.asSym().tryToUInt()

        fun TACExpr.tryToScalar() = tryToUInt()?.toScalar()
        fun TACSymbol.tryToScalar() = this.asSym().tryToScalar()

        fun TACCmd.Simple.ByteLongCopy.tryGetStride() = meta[LONG_COPY_STRIDE] ?: fail()

        val replacement: CommandWithRequiredDecls<TACCmd.Simple>? = if (lcmd.isMemoryAccess()) {
            when {
                cmd is TACCmd.Simple.AssigningCmd.ByteStore -> {
                    cmd.loc.tryToScalar()?.let { scalar ->
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(scalar, cmd.value.asSym(), cmd.meta).withDecls(scalar)
                    }
                }

                cmd is TACCmd.Simple.AssigningCmd.ByteLoad -> {
                    cmd.loc.tryToScalar()?.let { scalar ->
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(cmd.lhs, scalar.asSym(), cmd.meta).withDecls(scalar)
                    }
                }

                // For ByteLongCopy, we unroll the copy into individual scalar assignments
                cmd is TACCmd.Simple.ByteLongCopy -> when {
                    // Copying out of memory
                    cmd.srcBase == TACKeyword.MEMORY.toVar() && cmd.dstBase != TACKeyword.MEMORY.toVar() -> {
                        cmd.tryGetStride()?.let { stride ->
                            cmd.srcOffset.tryToUInt()?.let { srcOffset ->
                                cmd.length.tryToUInt()?.let { length ->
                                    mergeMany(
                                        (0U ..< length step stride).map { i ->
                                            val scalar = (srcOffset + i).toScalar()
                                            expr {
                                                cmd.dstOffset.asSym() add i.toLong().asTACExpr
                                            }.letVar { dstLoc ->
                                                TACCmd.Simple.AssigningCmd.ByteStore(
                                                    loc = dstLoc.s,
                                                    value = scalar,
                                                    base = cmd.dstBase,
                                                    meta = cmd.meta
                                                ).withDecls()
                                            }
                                        }
                                    )
                                }
                            }
                        }
                    }

                    // Copying into memory
                    cmd.srcBase != TACKeyword.MEMORY.toVar() && cmd.dstBase == TACKeyword.MEMORY.toVar() -> {
                        cmd.tryGetStride()?.let { stride ->
                            cmd.dstOffset.tryToUInt()?.let { dstOffset ->
                                cmd.length.tryToUInt()?.let { length ->
                                    mergeMany(
                                        (0U ..< length step stride).map { i ->
                                            val scalar = (dstOffset + i).toScalar()
                                            expr {
                                                cmd.srcOffset.asSym() add i.toLong().asTACExpr
                                            }.letVar { srcLoc ->
                                                TACCmd.Simple.AssigningCmd.ByteLoad(
                                                    lhs = scalar,
                                                    loc = srcLoc.s,
                                                    base = cmd.srcBase,
                                                    meta = cmd.meta
                                                ).withDecls(scalar)
                                            }
                                        }
                                    )
                                }
                            }
                        }
                    }

                    // Copying memory to memory
                    cmd.srcBase == TACKeyword.MEMORY.toVar() && cmd.dstBase == TACKeyword.MEMORY.toVar() -> {
                        cmd.tryGetStride()?.let { stride ->
                            cmd.srcOffset.tryToUInt()?.let { srcOffset ->
                                cmd.dstOffset.tryToUInt()?.let { dstOffset ->
                                    cmd.length.tryToUInt()?.let { length ->
                                        mergeMany(
                                            (0U ..< length step stride).map { i ->
                                                val src = (srcOffset + i).toScalar()
                                                val dst = (dstOffset + i).toScalar()
                                                assign(dst) { src.asSym() }
                                            }
                                        )
                                    }
                                }
                            }
                        }
                    }

                    // Copying non-memory to non-memory, doesn't concern us
                    else -> null
                }

                // Skip zero-length reads (reverts, etc)
                cmd is TACCmd.Simple.SingletonLongRead && cmd.length == TACSymbol.Zero -> null
                cmd is TACCmd.Simple.LongAccess && cmd.length == TACSymbol.Zero -> null

                // Skip the memory init; it just havocs memory
                MEMORY_INITIALIZATION in cmd.meta -> null

                // Unsupported memory access!
                else -> fail()
            }
        } else {
            // Rewrite any memory access expressions in the command
            object : DefaultTACCmdMapper() {
                override val exprMapper = object : QuantDefaultTACExprTransformer() {
                    // Replace select(mem, loc) with the corresponding scalar var
                    override fun transformSelect(acc: QuantDefaultTACExprTransformer.QuantVars, base: TACExpr, loc: TACExpr, tag: Tag?) =
                        if (base.getAs<TACExpr.Sym>()?.s == TACKeyword.MEMORY.toVar()) {
                            loc.tryToScalar()?.asSym() ?: loc
                        } else {
                            super.transformSelect(acc, base, loc, tag)
                        }

                    // Fail if we encounter TACKeyword.MEMORY outside of a select
                    override fun transformFreeVar(acc: QuantDefaultTACExprTransformer.QuantVars, exp: TACExpr.Sym.Var) =
                        super.transformFreeVar(acc, exp).also {
                            if (exp.s == TACKeyword.MEMORY.toVar()) {
                                fail<Any>()
                            }
                        }
                }
            }.map(cmd).takeIf { it != cmd }?.withDecls()
        }

        ptr `to?` replacement
    }.toList()

    if (failures.isNotEmpty()) {
        Logger.alwaysWarn("${code.name}: failed to scalarize memory accesses")
        failures.distinct().sortedBy { it.ptr }.forEach {
            logger.info { "${code.name}: at $it" }
        }

        CVTAlertReporter.reportAlert(
            CVTAlertType.ANALYSIS,
            CVTAlertSeverity.WARNING,
            null,
            "Unable to optimize memory accesses for ${code.name}",
            null
        )

        return code
    }

    val patched = code.patching { p ->
        for ((ptr, impl) in replacements) {
            p.replaceCommand(ptr, impl)
        }

        p.addBefore(
            CmdPointer(code.entryBlockId, 0),
            mergeMany(
                scalars.values.map {
                    assignHavoc(it)
                }
            )
        )
    }

    return CoreToCoreTransformer(ReportTypes.DSA, TACDSA::simplify).applyTransformer(patched)
}
