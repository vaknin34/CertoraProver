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

import config.Config
import datastructures.add
import datastructures.mutableMultiMapOf
import smt.FreeIdentifierCollector
import smt.GenerateEnv
import smt.axiomgenerators.*
import smt.axiomgenerators.StringExpressionPair.Companion.toExpr
import smt.newufliatranslator.AxiomGenerator
import smt.solverscript.LExpressionFactory
import smt.solverscript.SmtTheory
import smt.solverscript.functionsymbols.*
import statistics.data.BitwiseAxiomGeneratorStats
import utils.containsAny
import vc.data.LExpression
import vc.data.LExpressionWithEnvironment
import java.math.BigInteger


class BitwiseAxiomGenerator(
    val lxf: LExpressionFactory,
    val targetTheory: SmtTheory,
    private val linearMathAxiomGenerator: LinearMathAxiomGenerator?
) : AxiomGenerator() {

    private val precision =
        if (!targetTheory.isNia) {
            Config.Smt.bitwisePrecisionLIAoverride.get().let {
                if (it != -1) it else Config.Smt.bitwisePrecision.get()
            }
        } else {
            Config.Smt.bitwisePrecision.get()
        }

    private val defs = BitwiseAxiomsDefs(lxf, precision)

    private val axioms = AxiomSet(lxf)

    private val statsBuilder = BitwiseAxiomGeneratorStats.Builder()
    override val stats
        get() = statsBuilder.build()

    // tracks all expressions e found in a multiplication exactly of the form "e * EVM_BITWIDTH"

    private val binaryApps = mutableMultiMapOf<BinaryIntAxiomDef, LExpressionWithEnvPair>()
    private val unaryApps = mutableMultiMapOf<UnaryIntAxiomDef, LExpressionWithEnvironment>()

    private val cachedFreeIdentifierCollector = FreeIdentifierCollector(withCache = true)

    override fun visit(e: LExpression, env: GenerateEnv) {
        if (precision == 0) {
            return
        }
        if (e !is LExpression.ApplyExpr) {
            return
        }
        if (!env.isEmpty() && // <- optimization to save the collect call below in case
                cachedFreeIdentifierCollector.collect(e).containsAny(env.quantifiedVariables)) {
            /*
             * we currently just omit axioms that would be quantified
             *
             * background:
             * I (alex) discussed with Yoav -- apparently these axioms weren't created before this PR
             * (https://certora.atlassian.net/browse/CERT-2953) either, but back then it
             * was by accident, because Identifier.Variable and Identifier.Constant were different even when their
             * names were the same...
             * So this preserves the status quo.
             * To actually add these axioms or do something smart about them is future work; when we just add them now,
             * we get timeouts on a bunch of our tests (and very likely also on many more customer runs)
             */
            return
        }

        fun add1(axiom: BinaryIntAxiomDef, e1: LExpression, e2: LExpression) =
            binaryApps.add(axiom, LExpressionWithEnvironment(e1, env) to LExpressionWithEnvironment(e2, env))

        fun add1(axiom: UnaryIntAxiomDef, e: LExpression) =
            unaryApps.add(axiom, LExpressionWithEnvironment(e, env))

        fun addArgs(axiom: UnaryIntAxiomDef) =
            e.args.forEach { add1(axiom, it) }

        /** visits all the interesting generated sub expressions */
        fun visitGeneratedAxioms(def: UnaryIntAxiomDef, arg: LExpression) {
            def.unfold(arg).traverse { subE ->
                if (subE.isApplyOf<TheoryFunctionSymbol.Binary.IntMod>()) {
                    linearMathAxiomGenerator?.visit(subE, env)
                }
                if (subE.isApplyOf<NonSMTInterpretedFunctionSymbol.Binary.BitwiseAnd>()) {
                    visit(subE, env)
                }
            }
        }


        when (val f = e.f) {
            is NonSMTInterpretedFunctionSymbol.Binary -> {
                val (lhs, rhs) = e.args
                when (f) {

                    is NonSMTInterpretedFunctionSymbol.Binary.BitwiseAnd -> {
                        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Bitwise.UninterpBwAnd)
                        addArgs(defs.combinedBwAndUnary)

                        statsBuilder.bwands++

                        fun addMaskApp(mask: BigInteger, arg: LExpression) {
                            val def = defs.combinedBwAndWithMask(mask)
                            if (add1(def, arg)) {
                                visitGeneratedAxioms(def, arg)
                            }
                        }

                        when (e.lhs.isConst to e.rhs.isConst) {
                            true to false -> addMaskApp(lhs.asConst, rhs)
                            false to true -> addMaskApp(rhs.asConst, lhs)
                            false to false -> add1(defs.combinedBwAndBinary, lhs, rhs)
                            true to true -> axioms.addX(listOf(), env, "bitwise def" toExpr {
                                e eq litInt(lhs.asConst.and(rhs.asConst))
                            })
                        }
                    }

                    is NonSMTInterpretedFunctionSymbol.Binary.BitwiseOr -> {
                        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Bitwise.UninterpBwOr)
                        addArgs(defs.combinedBwOrUnary)

                        statsBuilder.bwors++

                        fun addMaskApp(mask: BigInteger, arg: LExpression) {
                            val def = defs.combinedBwOrWithMask(mask)
                            if (add1(def, arg)) {
                                visitGeneratedAxioms(def, arg)
                            }
                        }

                        when (e.lhs.isConst to e.rhs.isConst) {
                            true to false -> addMaskApp(lhs.asConst, rhs)
                            false to true -> addMaskApp(rhs.asConst, lhs)
                            false to false -> add1(defs.combinedBwOrBinary, lhs, rhs)
                            true to true -> axioms.addX(listOf(), env, "bitwise def" toExpr {
                                e eq litInt(lhs.asConst.or(rhs.asConst))
                            })
                        }
                    }

                    is NonSMTInterpretedFunctionSymbol.Binary.BitwiseXor -> {
                        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Bitwise.UninterpBwXOr)
                        addArgs(defs.combinedBwXorUnary)

                        statsBuilder.bwxors++

                        when (e.lhs.isConst to e.rhs.isConst) {
                            true to true -> axioms.addX(listOf(), env, "bitwise def" toExpr {
                                e eq litInt(lhs.asConst.xor(rhs.asConst))
                            })

                            else -> add1(defs.combinedBwXorBinary, lhs, rhs)
                        }
                    }

                    else -> Unit
                }
            }

            is AxiomatizedFunctionSymbol.Bitwise.SignExtend -> {
                val arg = e.arg
                val bits = (f.i + 1) * 8
                val lowOnes = BigInteger.TWO.pow(bits) - BigInteger.ONE
                val onlyLows = lxf { arg bitwiseAnd litInt(lowOnes) }
                visit(onlyLows, env) // get all bitwise-and axioms
                add1(defs.signExtend(f.i), arg)

                statsBuilder.signExtends++
            }


            is AxiomatizedFunctionSymbol -> when (e.f) {
                is AxiomatizedFunctionSymbol.Bitwise.UninterpBwAnd,
                AxiomatizedFunctionSymbol.Bitwise.UninterpBwOr,
                AxiomatizedFunctionSymbol.Bitwise.UninterpBwXOr,
                AxiomatizedFunctionSymbol.UninterpMul ->
                    error {
                        "we don't do this replacement until GeneratorContainer.postprocess " +
                            "-- thus shouldn't reach this point "
                    }

                else -> Unit
            }
            else -> Unit
        }
    }


    override fun yield(axiomContainer: AxiomContainer) = timeIt("Yield") {
        unaryApps.forEach { (axiom, set) ->
            axiom.addAllToContainer(axiomContainer, set)
        }
        binaryApps.forEach { (axiom, set) ->
            axiom.addAllToContainer(axiomContainer, set)
        }
        axiomContainer.addAll(axioms)
    }

}
