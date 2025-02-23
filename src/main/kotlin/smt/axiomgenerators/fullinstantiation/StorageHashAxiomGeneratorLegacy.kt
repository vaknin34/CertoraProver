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
import datastructures.stdcollections.*
import evm.MAX_EVM_UINT256
import smt.GenerateEnv
import smt.axiomgenerators.AxiomContainer
import smt.axiomgenerators.DefType
import smt.newufliatranslator.StorageHashAxiomGenerator
import smt.solverscript.LExpressionFactory
import smt.solverscript.functionsymbols.*
import tac.MetaMap
import tac.Tag
import utils.*
import vc.data.HashFamily
import vc.data.LExpression
import vc.data.lexpression.ChainedLExpressionTransformer
import vc.data.lexpression.PlainLExpressionTransformer
import java.math.BigInteger


/**
 * Axiom generator for the "legacy" way of dealing with storage-related hashing.
 * Uses large integers to model the "non-collision with large gaps" assumption that EVM makes on the keccak hash
 * function.
 *
 * NB: With the default [gapSize] of 2^256 this does not work with BV logics; it might for smaller gap sizes though
 *   (implications would need to be thought through a bit more).
 *
 * Building and axiomatizing the function step by step (conceptual overview, notes on implementation below).
 * For each [NonSMTInterpretedFunctionSymbol.Hash.SimpleHashN] function symbol
 * 1. define a bijection h_n : Int^n -> Int
 * 2. for `gap_size` construct the function add_gap : Int -> Int with add_gap(x) = x * gap_size
 * 3. build the final function for [NonSMTInterpretedFunctionSymbol.Hash.SimpleHashN] as
 *        `simple_hash_n(x1, ..., xn) = add_gap(arity_disambig(n, h_n(x1, ..., xn)))`
 * Then, in order to make sure that the outputs of different simple_hash_n functions cannot collide, add arity
 * disambiguation axioms using [BijectionAxiomHelper.addDisambiguation].
 *
 * Implementation-wise, we
 *  - collect all applications of [NonSMTInterpretedFunctionSymbol.Hash.SimpleHashN] in the program, call them
 *    `hash_apps`
 *  - use the argument tuples of `hash_apps` to add bijection axioms for the `h_n`s
 *  - use the full `applyExp`s in `hash_apps` to add bijection axioms for `arity_disambig`
 *  - use a define-fun to put everything together
 *  - furthermore We add an axiom that makes sure that hashes are never in the interval `[0, [maxSoliditySlot])`.
 *   (Solidity places the storage slots for contract fields at the beginning of storage.)
*
 *  Note, we might want to rename "legacy" with a better name some time.
 */
class StorageHashAxiomGeneratorLegacy(
    lxf: LExpressionFactory,
    // NB: gapSize must be in sync with [ConstantComputerWithHashSimplificiations] if that simplification is used
    private val gapSize: BigInteger,
    maxSoliditySlot: BigInteger = Config.MaxBaseStorageSlot.get(),
) : StorageHashAxiomGenerator(lxf, maxSoliditySlot, Tag.Int) {

    companion object {
        /** Convenience functions for skeys */
        private fun LExpressionFactory.toSkey(x: LExpression) =
            applyExp(AxiomatizedFunctionSymbol.Hash.ToSkey, x) as LExpression.ApplyExpr
        private fun LExpressionFactory.fromSkey(x: LExpression) =
            applyExp(AxiomatizedFunctionSymbol.Hash.FromSkey, x) as LExpression.ApplyExpr

    }

    override val skeyTransformer: PlainLExpressionTransformer = skeyToIntTransformer(Tag.Int)
    private val toSkeyApps: MutableSet<LExpression.ApplyExpr> = mutableSetOf()
    private val fromSkeyApps: MutableSet<LExpression.ApplyExpr> = mutableSetOf()
    private val skeyAdditions: MutableSet<LExpression.ApplyExpr> = mutableSetOf()

    /**
     * Treat skeys as integers --> eliminate to_skey and skey_add in favour of integer symbols/operations
     */
    override val postProcessSkeyTransformer: PlainLExpressionTransformer = ChainedLExpressionTransformer(
        object : PlainLExpressionTransformer() {
            override fun applyExprPost(exp: ApplyExpr): IntermediateLExp? = when (val f = exp.f) {
                is NonSMTInterpretedFunctionSymbol.Hash.SimpleHashN ->
                    runIf(f.hashFamily is HashFamily.Keccack) {
                        exp.copy(f = AxiomatizedFunctionSymbol.Hash.SimpleHashN(Tag.Int, f.arity, HashFamily.Keccack))
                    }
                is NonSMTInterpretedFunctionSymbol.Hash.SkeyAdd ->
                    exp.copy(f = TheoryFunctionSymbol.Vec.IntAdd)
                NonSMTInterpretedFunctionSymbol.Hash.Basic ->
                    exp.arg.lift()
                NonSMTInterpretedFunctionSymbol.Hash.FromSkey ->
                    exp.copy(f = AxiomatizedFunctionSymbol.Hash.FromSkey)
                NonSMTInterpretedFunctionSymbol.Hash.ToSkey ->
                    exp.copy(f = AxiomatizedFunctionSymbol.Hash.ToSkey)
                else -> null
            }
        },
        skeyToIntTransformer(Tag.Int)
    )

    private val arityToHashApps = mutableMultiMapOf<Int, LExpression.ApplyExpr>()
    private lateinit var hashParamVars: List<LExpression.Identifier>

    override fun visit(e: LExpression, env: GenerateEnv) {
        when (e) {
            is LExpression.ApplyExpr -> {
                when (val f = e.f) {
                    is NonSMTInterpretedFunctionSymbol.Hash.SimpleHashN -> {
                        if (f.hashFamily is HashFamily.Keccack) {
                            arityToHashApps.add(e.args.size, postProcessSkeyTransformer(e) as LExpression.ApplyExpr)
                            lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Hash.SimpleHashN(
                                Tag.Int,
                                e.args.size,
                                HashFamily.Keccack
                            ))
                        }
                    }
                    is NonSMTInterpretedFunctionSymbol.Hash.SkeyAdd -> {
                        skeyAdditions.add(postProcessSkeyTransformer(e) as LExpression.ApplyExpr)
                    }
                    is NonSMTInterpretedFunctionSymbol.Hash.ToSkey -> {
                        toSkeyApps.add(postProcessSkeyTransformer(e) as LExpression.ApplyExpr)
                    }
                    is NonSMTInterpretedFunctionSymbol.Hash.FromSkey -> {
                        fromSkeyApps.add(postProcessSkeyTransformer(e) as LExpression.ApplyExpr)
                    }
                    is AxiomatizedFunctionSymbol.Hash.SimpleHashN ->
                        error("not expecting hash function symbol \"${e.f}\" to come out of TAC directly")
                    else -> Unit // do nothing
                }
            }
            else -> Unit // do nothing
        }
        super.visit(e, env)
    }

    override fun beforeScriptFreeze() {
        arityToHashApps.keys.forEach { arity ->
            lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Hash.SimpleHashNPre(arity))
            (0 until arity).forEach { i ->
                lxf.registerFunctionSymbol(
                    AxiomatizedFunctionSymbol.Hash.PointwiseInversePerHashFamily(i, HashFamily.Keccack)
                )
            }
        }

        hashParamVars = List(arityToHashApps.keys.maxOrNull() ?: 0) {
            lxf.freshVariable("hashParam!$it", Tag.Int)
        }
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Hash.ToSkey)
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Hash.FromSkey)
        super.beforeScriptFreeze()
    }

    override fun declarationFilter(fs: FunctionSymbol): Boolean = filterSkeyDeclarations(fs)

    /**
     * Define `simple_hash_n(x1, ..., xn)` as `(simple_hash_pre_n(x1, ..., xn) + 1) * [gapSize]`
     *
     * Note that arity disambiguation happens in [yield] using the [BijectionAxiomHelper.addDisambiguation]
     * infrastructure.
     * */
    override fun yieldDefineFuns(): List<DefType> {
        val res = mutableListOf<DefType>()
        arityToHashApps.entries.forEach { (arity, _) ->
            val hashParams = hashParamVars.subList(0, arity)
            res.add(
                DefType(
                    id = AxiomatizedFunctionSymbol.Hash.SimpleHashN(Tag.Int, arity, HashFamily.Keccack),
                    args = hashParams,
                    ret = Tag.Int,
                    def = lxf {
                        (
                                applyExp(
                                    AxiomatizedFunctionSymbol.Hash.SimpleHashNPre(arity),
                                    hashParams
                                ) + ONE // move things out of the [0, gapSize) range by adding 1 here
                                ) * litInt(gapSize)
                    },
                )
            )
        }
        return res + super.yieldDefineFuns()
    }

    override fun yield(axiomContainer: AxiomContainer) = timeIt("Yield") {
        /** copy method that goes through [LExpressionFactory]'s checks. */
        fun LExpression.ApplyExpr.checkedCopy(
            f: FunctionSymbol = this.f,
            args: List<LExpression> = this.args,
            meta: MetaMap = this.meta,
        ): LExpression.ApplyExpr = lxf.applyExp(f, args, meta) as LExpression.ApplyExpr

        val hashApps = arityToHashApps.values.flatMapToSet { it }

        // take all hash arguments, wrap them in from_skey, and add those to [fromSkeyApps]
        // reason: we might need those terms for storage path parsing in the context of storage comparison
        //  (they're also added to terms of interest, either one-by-one, or from_skey as a whole)
        hashApps.forEach { e ->
            e.args.forEach { arg ->
                fromSkeyApps.add(
                    lxf {
                        applyExp(AxiomatizedFunctionSymbol.Hash.FromSkey, arg) as LExpression.ApplyExpr
                    }
                )
            }
        }

        // axiomatize the SimpleHashNPre function as a bijection (injection) by adding an inverse function
        BijectionAxiomHelper.addPointwiseInverseFunctions(
            axiomContainer,
            { i -> AxiomatizedFunctionSymbol.Hash.PointwiseInversePerHashFamily(i, HashFamily.Keccack) },
            hashApps
                .map { hashApp ->
                    hashApp.copyFs(
                        lxf,
                        AxiomatizedFunctionSymbol.Hash.SimpleHashNPre(hashApp.args.size)
                    ) as LExpression.ApplyExpr
                },
        )

        arityToHashApps.entries.forEach { (arity, hashApps) ->

            fun makeSimpleHashPre(hashApp: LExpression.ApplyExpr): LExpression.ApplyExpr =
                when (hashApp.f) {
                    is NonSMTInterpretedFunctionSymbol.Hash.SimpleHashN -> {
                        hashApp.checkedCopy(
                            f = AxiomatizedFunctionSymbol.Hash.SimpleHashNPre(arity)
                        )
                    }
                    is AxiomatizedFunctionSymbol.Hash.SimpleHashN ->
                        hashApp.checkedCopy(f = AxiomatizedFunctionSymbol.Hash.SimpleHashNPre(arity))

                    else -> {
                        `impossible!`
                    }
                }

            // note: arity disambiguation is not necessary any more, since we're keeping the length in bytes around
            //   (was done here before)

            if (gapSize < maxSoliditySlot) {
                /* in addition to the injectivity, we ensure that no hash ends up in the reserved area at the beginning
                 * of storage -- but only if the "+ 1" in the define-fun isn't enough because gapSize is lower than
                 * reservedSlots */
                hashApps.forEach { hashapp ->
                    axiomContainer.addAxioms(
                        "first $maxSoliditySlot storage slots are reserved for contract fields" to
                                {
                                    applyExp(
                                        AxiomatizedFunctionSymbol.Hash.SimpleHashN(Tag.Int, arity, HashFamily.Keccack),
                                        hashapp.args
                                    ) gt litInt(maxSoliditySlot)
                                }
                    )
                }
            }

            // use only the positive number space
            //   kind of redundant perhaps, if the slot constraint is there .. OLD: (otherwise we don't respect the reserved solidity slots after all)
            // this needs to apply to the arity_disambig function because otherwise the `+ 1` trick does not work
            hashApps.forEach { hashApp ->
                axiomContainer.addAxioms(
                    "all hashes (even before large gaps) are non-negative" to
                        { makeSimpleHashPre(hashApp) ge ZERO }
                )
            }
        }

        // to_skey and from_skey are inverses of each other
        BijectionAxiomHelper.axiomatizeFunctionsAsInverses(
            axiomContainer,
            lxf,
            AxiomatizedFunctionSymbol.Hash.ToSkey,
            toSkeyApps.map { it.args },
            AxiomatizedFunctionSymbol.Hash.FromSkey,
            fromSkeyApps.map { it.args },
        )

        // from_skey should be in bv256 bounds
        // should be generalized in TODO CERT-1791
        arityToHashApps.forEachEntry { (_, apps) ->
            apps.forEach { app ->
                axiomContainer.addAxioms(
                    "0 <= from_skey(x) && from_skey(x) <= max_uintVMBW" to {
                        (litInt(0) le applyExp(AxiomatizedFunctionSymbol.Hash.FromSkey, app)) and
                            (applyExp(AxiomatizedFunctionSymbol.Hash.FromSkey, app) le litInt(MAX_EVM_UINT256))
                    }
                )
            }
        }

        // x <= max_solidity_slot => to_skey(x) = x
        toSkeyApps.forEach { app ->
            val arg = app.args.single()
            axiomContainer.addAxioms(
                "x <= max_solidity_slot => to_skey(x) = x" to {
                    (arg le maxSoliditySlotLExp) implies (toSkey(arg) eq arg)
                }
            )
        }
        // x > max_uint => from_skey(x) > max_solidity_slot
        fromSkeyApps.forEach { app ->
            val arg = app.args.single()
            axiomContainer.addAxioms(
                "x > max_uint => from_skey(x) > max_solidity_slot" to {
                    (arg gt litInt(MAX_EVM_UINT256)) implies (fromSkey(arg) gt maxSoliditySlotLExp)
                }
            )
        }
        // x > max_solidity_slot => (to_skey x) > max_solidity_slot
        toSkeyApps.forEach { app ->
            val arg = app.args.single()
            axiomContainer.addAxioms(
                "x > max_solidity_slot => (to_skey x) > max_solidity_slot" to {
                    (arg gt maxSoliditySlotLExp) implies (toSkey(arg) gt maxSoliditySlotLExp)
                },
            )
        }
        // to_skey(<large constant in code>) = <large constant in code>
        largeConstantsInCode.forEach { c ->
            axiomContainer.addAxioms(
                "to_skey(<large constant in code>) = <large constant in code>" to
                        { toSkey(litInt(c)) eq litInt(c) },
                "from_skey(<large constant in code>) = <large constant in code>" to
                        { fromSkey(litInt(c)) eq litInt(c) }
            )
        }

        // (from_skey (skey_add <skey> <offset>)) = (+ (from_skey <skey>) <offset>)))
        skeyAdditions.forEach { skeyAdd ->
            val (skey, offset) = skeyAdd.args
            axiomContainer.addAxioms(
                "(from_skey (skey_add <skey> <offset>)) = (+ (from_skey <skey>) <offset>)))" to
                    { (fromSkey(skeyAdd)) eq (fromSkey(skey) intAdd offset) }
            )
        }
    }
}
