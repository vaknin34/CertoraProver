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

package smt.axiomgenerators.fullinstantiation

import analysis.split.Ternary.Companion.isPowOf2
import config.Config
import datastructures.add
import datastructures.mutableMultiMapOf
import datastructures.stdcollections.*
import log.*
import smt.GenerateEnv
import smt.axiomgenerators.AxiomContainer
import smt.axiomgenerators.AxiomSet
import smt.axiomgenerators.BasicMathAxiomsDefs
import smt.axiomgenerators.Overapproximation
import smt.newufliatranslator.AxiomGenerator
import smt.solverscript.LExpressionFactory
import smt.solverscript.functionsymbols.*
import tac.Tag
import utils.*
import vc.data.LExpression
import java.math.BigInteger


private val logger = Logger(LoggerTypes.SMT_MATH_AXIOMS)

/**
 * Adds some axioms when using bit-vector theory.
 */
class BVMathAxiomGenerator(val lxf: LExpressionFactory) : AxiomGenerator() {

    private val basicMathAxiomsDefs = BasicMathAxiomsDefs(lxf)

    private val axioms = AxiomSet(lxf)

    /** The set of constant bases we see in `pow` expressions */
    private val bases = mutableSetOf<BigInteger>()
    private val constPowerExprs = mutableMultiMapOf<Int, LExpression>()


    override fun visit(e: LExpression, env: GenerateEnv) {
        if (e !is LExpression.ApplyExpr) {
            return
        }
        when (e.f) {
            is NonSMTInterpretedFunctionSymbol.Binary.Exp,
            is AxiomatizedFunctionSymbol.UninterpExp -> {
                // generate axioms for bases that are not powers of 2.
                // Bases that are powers of two were either replaced by shift-left when translating from TAC
                // (for `TACExpr.BinOp.Exponent`), or will be replaced at `ExpNormalizerBv` (for `TACExpr.BinOp.IntExponent`).
                if (e.lhs.isConst && !e.lhs.asConst.isPowOf2) {
                    bases += e.lhs.asConst
                }
                if (e.rhs.isActuallyInt) {
                    e.rhs.asConst.toIntOrNull()?.takeIf {
                        val res = it <= Config.Smt.MaxPreciseConstantExponent.get()
                        if (!res) {
                            @Overapproximation("constant exponentiation: exponent too high")
                            logger.warn { "Constant exponentiation with too-high exponent -- overapproximating it. " +
                                "Expression: $e" }
                        }
                        res
                    }?.let { i -> constPowerExprs.add(i, e.lhs) }
                }

                if (e.f is NonSMTInterpretedFunctionSymbol.Binary.Exp) { // this will turn into UninterpExp by ExpNormalizer..
                    lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.UninterpExp(Tag.Int))
                    lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.UninterpExp(Tag.Bit256))
                }
            }

            else -> Unit
        }
        return
    }

    override fun beforeScriptFreeze() {
        constPowerExprs.keys.forEach { basicMathAxiomsDefs.constantPowAxiom(it) } // registers them as a side effect
        super.beforeScriptFreeze()
    }

    override fun yield(axiomContainer: AxiomContainer) {
        for (base in bases) {
            axiomContainer.addAxiom(basicMathAxiomsDefs.powAxiom(base))
        }
        constPowerExprs.forEachEntry { (pow, exprs) ->
            basicMathAxiomsDefs.constantPowAxiom(pow).addAllToContainer(axiomContainer, exprs)
        }
        axiomContainer.addAll(axioms)
    }
}
