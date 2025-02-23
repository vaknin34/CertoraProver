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

package analysis.smtblaster

import analysis.CmdPointer
import analysis.TACBlock
import log.Logger
import log.LoggerTypes
import smtlibutils.data.FactorySmtScript
import smtlibutils.data.SmtExp
import smtlibutils.data.SmtIntpFunctionSymbol
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol
import java.math.BigInteger

private val logger = Logger(LoggerTypes.BIT_BLAST)

/**
 * A simple translator from (straight-line) TACCmds to the theory of BitVectors. After all commands have been translated, the
 * user may generate a VC which is then conjoined with the translation and automatically discharged with Z3.
 *
 * Used mainly for checking low-level solidity operations against expected high-level behavior
 */
object BitBlaster {

    const val BV_TYPE = "(_ BitVec 256)"
    /**
     * Translate the code in [block] beginning at index [start] up to (but excluding) the index [end].
     *
     * [synthAssign] indicates commands within the range that should be overridden with an assignment from an arbitrary
     * Z3 identifier. These identifiers typically represent some nondeterministic input to the command.
     *
     * [env] is an optional mapping of variables to symbolic value names.
     *
     * [vcGen] accepts the mapping of variables to their Z3 identifiers at [end] and may return an aribtrary Z3
     * string. The BitBlaster checks for unsat, so the VC should assert a negation of the desired property.
     */
    fun blastCode(
        block: TACBlock,
        start: Int,
        end: Int,
        synthAssign: Map<CmdPointer, String>,
        env: Map<TACSymbol.Var, String> = mapOf(),
        blaster: IBlaster = Z3Blaster,
        alwaysDeclare: Set<String> = emptySet(),
        vcGen: SmtScriptBuilder<*, SmtExp>.(Map<TACSymbol.Var, String>) -> Boolean,
    ) : Boolean {
        var incr = 0
        val state = env.toMutableMap()
        fun nameFor(v: TACSymbol.Var): String {
            incr++
            return "${v.toSMTRep()}_$incr"
        }
        val script = SmtExpScriptBuilder(termBuilder = SmtExpBitVectorTermBuilder)
        val exprBlaster = object : SmtExpBitBlaster() {
            override fun blastExpr(e: TACExpr, vm: (TACSymbol.Var) -> String?): SmtExp? {
                if(e is TACExpr.BinOp.Exponent) {
                    val o1 = e.o1AsTACSymbol()
                    if (o1 !is TACSymbol.Const || o1.value != 256.toBigInteger()) {
                        logger.warn {
                            "Found an exponent command $e that could not be translated to a shift (giving up)"
                        }
                        return null
                    }
                    return super.blastExpr(e.o2, vm)?.let {
                        FactorySmtScript.apply(
                            SmtIntpFunctionSymbol.BV.BinOp.BvShL(256),
                            FactorySmtScript.bitvector(BigInteger.ONE, 256),
                            FactorySmtScript.apply(
                                SmtIntpFunctionSymbol.BV.BinOp.BvMul(256),
                                FactorySmtScript.bitvector(8.toBigInteger(), 256),
                                it
                            )
                        )
                    }
                } else {
                    return super.blastExpr(e, vm)
                }
            }
        }
        (synthAssign.values + env.values + alwaysDeclare).toSet().forEach {
            script.declare(it)
        }
        for (i in start until end) {
            val ltacCmd = block.commands[i]
            if(ltacCmd.ptr in synthAssign && ltacCmd.cmd is TACCmd.Simple.AssigningCmd) {
                val lhsName = nameFor(ltacCmd.cmd.lhs)
                script.define(lhsName) {
                    toIdent(synthAssign[ltacCmd.ptr]!!)
                }
                state[ltacCmd.cmd.lhs] = lhsName
                continue
            } else if (ltacCmd.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
                val lhsName = nameFor(ltacCmd.cmd.lhs)
                val rhs: TACExpr = ltacCmd.cmd.rhs
                val blastedRhs = exprBlaster.blastExpr(rhs) { v: TACSymbol.Var ->
                    state[v]
                }
                if(blastedRhs != null) {
                    script.define(lhsName) {
                        blastedRhs
                    }
                } else {
                    logger.warn {
                        "The translation of $ltacCmd returned null, assuming nondet"
                    }
                    logger.debug {
                        "The state $state"
                    }
                    script.declare(lhsName)
                }
                state.put(ltacCmd.cmd.lhs, lhsName)
            } else if (ltacCmd.cmd is TACCmd.Simple.AssigningCmd) {
                val lhsName = nameFor(ltacCmd.cmd.lhs)
                state.put(ltacCmd.cmd.lhs, lhsName)
                script.declare(lhsName)
            } else if(ltacCmd.cmd is TACCmd.Simple.AssumeCmd || ltacCmd.cmd is TACCmd.Simple.AssumeNotCmd) {
                logger.info {
                    "Ignoring assume @ % $ltacCmd"
                }
            } else if (ltacCmd.cmd !is TACCmd.Simple.LabelCmd &&
                ltacCmd.cmd !is TACCmd.Simple.NopCmd &&
                ltacCmd.cmd !is TACCmd.Simple.JumpdestCmd &&
                ltacCmd.cmd !is TACCmd.Simple.AnnotationCmd) {
                logger.warn { "Found command type we can't interpret $ltacCmd, giving up" }
                return false
            }
        }
        if(!vcGen(script, state)) {
            logger.warn { "User VC gen returned null, giving up" }
            logger.debug { "State at end: $state" }
            return false
        }
        script.checkSat()
        val vc_query = script.cmdList
        return blaster.blastSmt(vc_query)
    }
}
