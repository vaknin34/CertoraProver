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
import datastructures.stdcollections.*
import evm.EVM_MOD_GROUP256
import evm.twoToThe
import smt.GenerateEnv
import smt.axiomgenerators.AxiomContainer
import smt.newufliatranslator.StorageHashAxiomGenerator
import smt.solverscript.LExpressionFactory
import smt.solverscript.SmtTheory
import smt.solverscript.functionsymbols.*
import tac.Tag
import utils.*
import vc.data.*
import vc.data.lexpression.ChainedLExpressionTransformer
import vc.data.lexpression.PlainLExpressionTransformer
import java.math.BigInteger


/**
 *
 * Notes:
 *  - One thought was to forbid hash additions from wrapping around or going out of bounds, but according to our tests
 *    at least we don't want that --> e.g. in `Test/Datastructures/t1 rule existsAfterPushingUnsafe` our expected test
 *    result assumes that array offset computations _can_ wrap around
 *
 * @param axiomatizeKeccack only the [TACExpr.Vec.HashFamily.Keccack] (currently) is subject to large gaps
 *   axiomatization; if this is true, the keccack hashes are axiomatized here, otherwise they're ignored here (and have
 *   to be handled in one of the other [StorageHashAxiomGenerator]s).
 *
 */
class StorageHashAxiomGeneratorPlainInjectivity(
    lxf: LExpressionFactory,
    maxSoliditySlot: BigInteger = Config.MaxBaseStorageSlot.get(),
    private val targetTheory: SmtTheory,
    private val axiomatizeKeccack: Boolean,
) : StorageHashAxiomGenerator(lxf, maxSoliditySlot, Tag.Int) {

    override val skeyTransformer: PlainLExpressionTransformer? = runIf(axiomatizeKeccack) { skeyToIntTransformer(Tag.Int) }

    override val postProcessSkeyTransformer = ChainedLExpressionTransformer(
        object : PlainLExpressionTransformer("PlainInjectivity.postProcessSkey(axiomKeccak=$axiomatizeKeccack)") {
            override fun applyExprPost(exp: ApplyExpr): IntermediateLExp? {
                return when (exp.f) {
                    is NonSMTInterpretedFunctionSymbol.Hash.SimpleHashN ->
                        runIf(axiomatizeKeccack || exp.f.hashFamily !is HashFamily.Keccack) {
                            ApplyExpr(transformHashFs(exp.f), exp.args, exp.meta)
                        }

                    is NonSMTInterpretedFunctionSymbol.Hash.SkeyAdd ->
                        runIf(axiomatizeKeccack) {
                            lxf.intAdd(exp.args).lift()
                        }

                    NonSMTInterpretedFunctionSymbol.Hash.Basic,
                    NonSMTInterpretedFunctionSymbol.Hash.FromSkey,
                    NonSMTInterpretedFunctionSymbol.Hash.ToSkey ->
                        runIf(axiomatizeKeccack) {
                            exp.arg.lift()
                        }
                    else -> null
                }
            }
        },
        skeyTransformer
    )

    private val hashExpressionsInVcTransformed =
        mutableSetOf<ApplyExprView<AxiomatizedFunctionSymbol.Hash.SimpleHashN>>()

    private val skeyAddsInVc = mutableSetOf<ApplyExprView<NonSMTInterpretedFunctionSymbol.Hash.SkeyAdd>>()

    private val toSkeyArgsInVc = mutableSetOf<LExpression>()

    private fun transformHashFs(fs: NonSMTInterpretedFunctionSymbol.Hash.SimpleHashN) =
        AxiomatizedFunctionSymbol.Hash.SimpleHashN(Tag.Bit256, fs.arity, fs.hashFamily)

    override fun visit(e: LExpression, env: GenerateEnv) {
        when (e) {
            is LExpression.ApplyExpr -> when (val f = e.f) {
                is NonSMTInterpretedFunctionSymbol.Hash.SimpleHashN ->
                    if (axiomatizeKeccack || f.hashFamily !is HashFamily.Keccack) {
                        hashExpressionsInVcTransformed.add(
                            (postProcessSkeyTransformer(e) as LExpression.ApplyExpr).narrow<AxiomatizedFunctionSymbol.Hash.SimpleHashN>()
                        )
                    }
                is NonSMTInterpretedFunctionSymbol.Hash.SkeyAdd ->
                    if (axiomatizeKeccack) {
                        skeyAddsInVc.add(e.narrow())
                    }
               is NonSMTInterpretedFunctionSymbol.Hash.ToSkey ->
                    if (axiomatizeKeccack) {
                        toSkeyArgsInVc.add(e.args.first())
                    }
                else -> Unit
            }
            else -> Unit
        }
        super.visit(e, env)
    }

    /**
     * Steps:
     *  - make base hashes injective: axiomatize inverse function
     *  - ensure large gaps: axiomatize `base` function (which always evaluates to the original hash)
     *  - reserve basic slots:
     *    - constrain (base) hashes to be larger than max_solidity slot
     *    - axiomatize `base` of to_skey arguments depending on whether they exceed max_solidity_slot
     */
    override fun yield(axiomContainer: AxiomContainer) {
        check(hashExpressionsInVcTransformed.all { it.f.arity != 0 }) {
            "there should be no hash applications with no arguments at all, got " +
                "\"${hashExpressionsInVcTransformed.find { it.f.arity != 0 }}\""
        }

        /* injectivity and arity disambiguation */
        hashExpressionsInVcTransformed.groupBy { it.f.hashFamily }.forEachEntry { (hashFamily, hashApps) ->
            BijectionAxiomHelper.addPointwiseInverseFunctions(
                axiomContainer,
                { i -> AxiomatizedFunctionSymbol.Hash.PointwiseInversePerHashFamily(i, hashFamily) },
                hashApps.map { it.exp }
            )
        }

        // upper bounds (depends on hash family and targetTheory)
        val isBvLogic = targetTheory.arithmeticOperations == SmtTheory.ArithmeticOperations.BitVector
        hashExpressionsInVcTransformed.forEach { hashApp ->
            val exclusiveUpperBound =
                hashApp.f.hashFamily.resultSizeInBytes.let { rsib ->
                    check(rsib <= 32) { "unexpectedly high resultSizeInBytes: \"$rsib\"" }
                    if (rsib == 32) {
                        if (isBvLogic) {
                            null
                        } else {
                            EVM_MOD_GROUP256
                        }
                    } else {
                        twoToThe(rsib * 8)
                    }
                }
            if (exclusiveUpperBound != null) {
                axiomContainer.addAxiom(
                    lxf { hashApp.exp lt litInt(exclusiveUpperBound) },
                    description = "upper bound for ${hashApp.f}"
                )
            }
        }

        // all hash expression's outputs are larger than max_solidity_slot
        // note: it wasn't clear to me that we need this also for non-keccak hashes (which would have been handled by
        //   NoLargeGapsHashAxiomGenerator before)
        hashExpressionsInVcTransformed.forEach { hashApp ->
            axiomContainer.addAxioms(
                "max_solidity_slot < keccack(x)" to { maxSoliditySlotLExp lt hashApp.exp }
            )
        }


        /* constraints specific for keccak hashes / storage keys */
        val keccackApps = hashExpressionsInVcTransformed
            .filter { it.f.hashFamily is HashFamily.Keccack }

        fun base(arg: LExpression) = lxf.applyExp(AxiomatizedFunctionSymbol.Hash.PIBase, arg)

        // base(keccak(x)) == keccak(x)
        keccackApps.forEach { keccackApp ->
            axiomContainer.addAxiom(
                lxf { base(keccackApp.exp) eq keccackApp.exp },
                description = "base(keccak(x)) == keccak(x)"
            )
        }
        // base(skey_add(x, y)) == base(x)
        skeyAddsInVc.forEach { skeyAdd ->
            axiomContainer.addAxiom(
                lxf { base(skeyAdd.exp) eq base(skeyAdd.exp.args.first()) },
                description = "base(skey_add(x, y)) == base(x)"
            )
        }
        // to_skey(x) <= max_solidity_slot => base(to_skey(x)) == 0  (note that to_skey is the identity function here)
        toSkeyArgsInVc.forEach { toSkeyArg ->
            axiomContainer.addAxiom(
                lxf {
                    (toSkeyArg le maxSoliditySlotLExp) implies
                        (base(toSkeyArg) eq ZERO)
                },
                description = "to_skey(x) <= max_solidity_slot => base(to_skey(x)) == 0"
            )
        }




        // for all "large constants in code" c: base(c) == c
        /**
         * This axiom is needed to separate skey-additions on top of basic slots (i.e. < [maxSoliditySlot]) from the
         * large constants; conceptually it amounts to treating the large constants as hashes (which they are).
         * Note that in addition we also need to make sure that no (offset-0) hash equals a large constant. We enforce
         * that by the two axioms below.
         */
        if (axiomatizeKeccack) {
            largeConstantsInCode.forEach { c ->
                axiomContainer.addAxiom(
                    lxf {
                        base(litInt(c)) eq litInt(0)
                    },
                    description = "base(<largeConstantInCode>) == 0"
                )
            }
        }

        // The following two axioms enforce that all "large constants in code" are distinct from all keccack hash
        // applications.
        //  (no need to constrain skey_add applications here)
        //  this is done using the Boolean function `isLargeConstant`
        fun LExpressionFactory.isLargeConstant(arg: LExpression) =
            applyExp(AxiomatizedFunctionSymbol.Hash.PIIsLargeConstant, arg)

        if (axiomatizeKeccack) {
            // 1. for all "large constants in code" c: isLargeConstant(c)
            largeConstantsInCode.forEach { c ->
                axiomContainer.addAxioms(
                    "isLargeConstant(<largeConstantInCode>)" to { isLargeConstant(litInt(c)) }
                )
            }

            // 2. for all keccack applications: isLargeConstant(keccack(x)) == false
            keccackApps.forEach {  keccackApp ->
                axiomContainer.addAxioms(
                    "not isLargeConstant(keccack(x))" to { not(isLargeConstant(keccackApp.exp)) }
                )
            }
        }
    }

    override fun beforeScriptFreeze() {
        val hashFunctionSymbolsInVc = hashExpressionsInVcTransformed.mapToSet { it.f }

        val arities = mutableSetOf<Int>()
        val hashFamilies = mutableSetOf<HashFamily>()
        hashFunctionSymbolsInVc.forEach { hashFs ->
            hashFamilies.add(hashFs.hashFamily)
            arities.add(hashFs.arity)
        }

        hashFamilies.forEach { hashFamily ->
            arities.forEach { arity ->
                lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Hash.SimpleHashN(Tag.Bit256, arity, hashFamily))
                (0 until arity).forEach {  i ->
                    lxf.registerFunctionSymbol(
                        AxiomatizedFunctionSymbol.Hash.PointwiseInversePerHashFamily(i, hashFamily)
                    )
                }
            }
        }

        if (axiomatizeKeccack) {
            lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Hash.PIBase)
            lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Hash.PIIsLargeConstant)
        }
        super.beforeScriptFreeze()
    }

    override fun declarationFilter(fs: FunctionSymbol): Boolean =
        if (axiomatizeKeccack) {
            filterSkeyDeclarations(fs)
        } else {
            true
        }
}
