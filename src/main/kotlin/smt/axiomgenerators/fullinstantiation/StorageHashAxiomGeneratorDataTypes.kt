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
import evm.MAX_EVM_UINT256
import smt.GenerateEnv
import smt.axiomgenerators.AxiomContainer
import smt.axiomgenerators.DefType
import smt.axiomgenerators.UnaryAxiomDef
import smt.newufliatranslator.StorageHashAxiomGenerator
import smt.solverscript.LExpressionFactory
import smt.solverscript.functionsymbols.AxiomatizedFunctionSymbol
import smt.solverscript.functionsymbols.IFixedFunctionSignatures
import smt.solverscript.functionsymbols.IFixedFunctionSignatures.FixedFunctionSignatures
import smt.solverscript.functionsymbols.NonSMTInterpretedFunctionSymbol
import smt.solverscript.functionsymbols.isApplyOf
import smtlibutils.data.*
import statistics.*
import tac.Tag
import utils.*
import vc.data.HashFamily
import vc.data.LExpression
import vc.data.TACBuiltInFunction.Hash.Companion.skeySort
import vc.data.lexpression.*
import java.math.BigInteger


/**
 * Axiomatizes storage-related hashing using the theory of datatypes.
 * The "non-collision with large gaps" property that EVM assumes for the keccak hash function is modelled through the
 * implicit injectivity of data type constructors.
 *
 * Workflow:
 *  The program transformation in [AnnotateSkeyBifs] has introduced the `skey` sort in to the TAC program.
 *  This entails changing the types of some program variables and introducing applications of the function symbols
 *  `simple_hash`, `skey_add`, `basic`, `to_skey`, `from_skey`.
 *  Here, we translate those applications of datatype constructors as follows:
 *   - simple_hash(skey1, skey2) ~> SkeyNode2(skey1, skey2, 0)
 *   - basic(x)                  ~> SkeyNode1(nil, x)
 *   - skey_add(skey, y) = when (skey)
 *                            SkeyNode1 -> SkeyNode1(skey.first, intAdd(skey.second, y))
 *                            SkeyNode2 -> SkeyNode2(skey.first, skey.second, intAdd(skey.third, y))
 *                            etc.
 *              (assuming the datatypes have selectors named first, second, ...)
 *
 * future work / nice to have: it might be more elegant to have a separate datatype constructor for the large constants
 *  rather than making them basic (keeping e.g. a bit more the analogy with PlainInjectivity where they're their own
 *  base), would also save the exceptions in the [toSkeyNonBasic] axioms (might need extra thought)
 */
class StorageHashAxiomGeneratorDataTypes(
    lxf: LExpressionFactory,
    maxSoliditySlot: BigInteger = Config.MaxBaseStorageSlot.get(),
) : StorageHashAxiomGenerator(lxf, maxSoliditySlot, skeySort) {

    private val skeyVar = lxf.freshVariable("skey", sortOfStorageKeys)
    private val offsetVar = lxf.freshVariable("offset", Tag.Int)

    companion object {
        val dtSortDecLExp = LExpressionFactory.DatatypeDeclaration.SortDec(skeySort.name)
        val dtSortDecSmt = dtSortDecLExp.toSmtLib()
    }

    /** Invoked in [beforeScriptFreeze]; it must be invoked when all [largeConstantsInCode] have been collected,
     * and before symbols are frozen in [lxf]. */
    private val toSkeyNonBasicName = "to_skey_non_basic"
    private val toSkeyNonBasic by lazy {
        UnaryAxiomDef(
            lxf = lxf,
            name = toSkeyNonBasicName,
            description = "x > max_solidity_slot && <x does not equal one of the large literals> => " +
                    "(not (is (to_skey x) 'basic')))",
            tag = Tag.Int,
            exp = { arg ->
                and(
                    listOf(arg gt maxSoliditySlotLExp) + largeConstantsInCode.map { arg neq litInt(it) }
                ) implies not(
                    applyExp(AxiomatizedFunctionSymbol.SKeyDt.ToSkey(Tag.Int), arg) `is`
                            AxiomatizedFunctionSymbol.SKeyDt.Basic(Tag.Int)
                )
            }
        )
    }
    /** dual to [toSkeyNonBasic] */
    private val fromSkeyVsBasicName = "from_skey_vs_basic"
    private val fromSkeyVsBasic by lazy {
        fun fromSkey(x: LExpression) = lxf.applyExp(AxiomatizedFunctionSymbol.SKeyDt.FromSkey(Tag.Bit256), listOf(x))
        UnaryAxiomDef(
            lxf = lxf,
            name = fromSkeyVsBasicName,
            description = "(not (is x basic))) => " +
                "from_skey(x) > max_solidity_slot && <from_skey(x) does not equal one of the large literals>",
            tag = skeySort,
            exp = { arg ->
                not(arg `is` AxiomatizedFunctionSymbol.SKeyDt.Basic(Tag.Int)) implies
                    and(
                        listOf(fromSkey(arg) gt maxSoliditySlotLExp) + largeConstantsInCode.map { fromSkey(arg) neq litInt(it) }
                    )
            }
        )
    }


    /** I hate this workaround .. it's due to LExpressoinToSmtLib:153 (adding of ghost axioms, which use state from
     * LExpressionFactory .. -- we should untangle that sometime, then I hope this can go */
    private var symbolsFrozen = false


    private val nonBasicDtConstructors = mutableSetOf<AxiomatizedFunctionSymbol.SKeyDt>()

    private val timeStatsRecorder = ElapsedTimeStats()
    private val axiomNumberLogger = ScalarKeyValueStats<Int>()

    override fun getStatsRecorders(queryName: String): List<SDFeature<*>> = run {
        val query = queryName.toSDFeatureKey()
        val jclass = javaClass.simpleName.toString().toSDFeatureKey()
        listOf(timeStatsRecorder.fork(query, jclass), axiomNumberLogger.fork(query, jclass))
    }

    private val toSkeyApps: MutableSet<LExpression.ApplyExpr> = mutableSetOf()
    private val fromSkeyApps: MutableSet<LExpression.ApplyExpr> = mutableSetOf()

    private val skeyAdditions: MutableSet<LExpression.ApplyExpr> = mutableSetOf()

    private val skeyConstructors: MutableSet<LExpression.ApplyExpr> = mutableSetOf()

    // just for stat/debugging purposes -- make non-null if they should be collected
    private val skeyTerms: MutableSet<LExpression.ApplyExpr>? = null

    override fun visit(e: LExpression, env: GenerateEnv) {
        if (symbolsFrozen) {
            super.visit(e, env)
            return
        }
        if (e.isApplyOf<NonSMTInterpretedFunctionSymbol.Hash>() ) {
            when (val f = e.f) {
                is NonSMTInterpretedFunctionSymbol.Hash.SimpleHashN -> {
                    if (f.hashFamily is HashFamily.Keccack) {
                        nonBasicDtConstructors.add(AxiomatizedFunctionSymbol.SKeyDt.SkeyNode(f.arity))
                        skeyConstructors.add(e)
                    }
                }
                is NonSMTInterpretedFunctionSymbol.Hash.SkeyAdd -> {
                    skeyAdditions.add(e)
                }
                is NonSMTInterpretedFunctionSymbol.Hash.Basic -> {
                    /* nothing to do */
                }
                is NonSMTInterpretedFunctionSymbol.Hash.ToSkey -> {
                    // axioms for toSkey use the basic Skey, thus we need to register the function symbol here
                    // EDIT: basic skeys now have their own function symbol, which we always add
                    // nonBasicDtConstructors.add(AxiomatizedFunctionSymbol.SKeyDt.SkeyNode(1))
                    toSkeyApps.add(e)
                }
                is NonSMTInterpretedFunctionSymbol.Hash.FromSkey -> {
                    fromSkeyApps.add(e)
                }
                else -> Unit
            }
            skeyTerms?.add(e)
        }
        super.visit(e, env)
    }

    override val postProcessSkeyTransformer = object : PlainLExpressionTransformer("DataTypes.postProcessSkey") {
        override fun applyExprPost(exp: ApplyExpr): IntermediateLExp? =
            when (exp.f) {
                is NonSMTInterpretedFunctionSymbol.Hash.SimpleHashN ->
                    runIf(exp.f.hashFamily is HashFamily.Keccack) {
                        exp.copy(f = AxiomatizedFunctionSymbol.SKeyDt.SkeyNode(exp.args.size), args = exp.args + lxf.ZERO)
                    }
                is NonSMTInterpretedFunctionSymbol.Hash.SkeyAdd ->
                    exp.copy(f = AxiomatizedFunctionSymbol.SKeyDt.SkeyAdd(exp.rhs.tag))
                is NonSMTInterpretedFunctionSymbol.Hash.Basic ->
                    exp.copy(f = AxiomatizedFunctionSymbol.SKeyDt.Basic(exp.arg.tag))
                is NonSMTInterpretedFunctionSymbol.Hash.FromSkey ->
                    exp.copy(f = AxiomatizedFunctionSymbol.SKeyDt.FromSkey(Tag.Bit256))
                is NonSMTInterpretedFunctionSymbol.Hash.ToSkey ->
                    exp.copy(f = AxiomatizedFunctionSymbol.SKeyDt.ToSkey(exp.arg.tag))
                else -> null
            }
    }

    private fun LExpressionFactory.basicSkey(offset: LExpression) =
        applyExp(AxiomatizedFunctionSymbol.SKeyDt.Basic(offset.tag), offset)

    override fun yieldDefineFuns(): List<DefType> {
        fun selectSkeyNodeOperand(f: AxiomatizedFunctionSymbol.SKeyDt, i: Int, skey: LExpression): LExpression =
            lxf.applyExp(AxiomatizedFunctionSymbol.SKeyDt.SKeySelector(f, i, skeySort), listOf(skey))

        // define-fun for `skey_add`
        return listOf(
            with(lxf) {
                DefType(
                    AxiomatizedFunctionSymbol.SKeyDt.SkeyAdd(Tag.Int),
                    listOf(skeyVar, offsetVar),
                    sortOfStorageKeys,
                    nonBasicDtConstructors.map { fs ->
                        skeyVar `is` fs to
                                applyExp(fs,
                                    (fs.signature as IFixedFunctionSignatures).paramSorts
                                        .mapIndexed { index, tag ->
                                            when (tag) {
                                                sortOfStorageKeys -> selectSkeyNodeOperand(fs, index, skeyVar)
                                                Tag.Int -> selectSkeyNodeOperand(fs, index, skeyVar) intAdd offsetVar
                                                else -> `impossible!`
                                            }
                                        }
                                )
                    }.fold(
                        run {
                            val fs = AxiomatizedFunctionSymbol.SKeyDt.Basic(Tag.Int)
                            applyExp(fs, selectSkeyNodeOperand(fs, 0, skeyVar) intAdd offsetVar)
                        }
                    ) { acc, pair -> ite(pair.first, pair.second, acc) }
                )
            }
        )
    }

    override fun yield(axiomContainer: AxiomContainer) {

        // take all hash arguments, wrap them in from_skey, and add those to [fromSkeyApps]
        // reason: we might need those terms for storage path parsing in the context of storage comparison
        //  (they're also added to terms of interest, either one-by-one, or from_skey as a whole)
        skeyConstructors.forEach { e ->
            e.args.forEach { arg ->
                fromSkeyApps.add(
                    lxf {
                        applyExp(AxiomatizedFunctionSymbol.SKeyDt.FromSkey(Tag.Bit256), arg) as LExpression.ApplyExpr
                    }
                )
            }
        }

        // to_skey and from_skey are inverses of each other
        BijectionAxiomHelper.axiomatizeFunctionsAsInverses(
            axiomContainer,
            lxf,
            AxiomatizedFunctionSymbol.SKeyDt.ToSkey(Tag.Int),
            toSkeyApps.map { it.args },
            AxiomatizedFunctionSymbol.SKeyDt.FromSkey(Tag.Int),
            fromSkeyApps.map { it.args },
        )

        // from_skey should be in bv256 bounds
        // should be generalized in TODO CERT-1791
        skeyConstructors.forEach { app ->
            axiomContainer.addAxioms(
                "0 <= from_skey(x) && from_skey(x) <= max_uintVMBW" to {
                    (litInt(0) le applyExp(AxiomatizedFunctionSymbol.SKeyDt.FromSkey(Tag.Bit256), app)) and
                        (applyExp(AxiomatizedFunctionSymbol.SKeyDt.FromSkey(Tag.Bit256), app) le litInt(MAX_EVM_UINT256))
                }
            )
        }

        // x <= max_solidity_slot => to_skey(x) = basic(x)
        // also: to_skey never maps to `nil` -- (`nil` by itself is unused by us)
        toSkeyApps.forEach { app ->
            val arg = app.args.single()
            axiomContainer.addAxioms(
                "x <= max_solidity_slot => to_skey(x) = basic(x)" to {
                    (arg le maxSoliditySlotLExp) implies
                            (applyExp(AxiomatizedFunctionSymbol.SKeyDt.ToSkey(arg.tag), arg) eq basicSkey(arg))
                },
            )
        }


        // x > max_solidity_slot && <x does not equal one of the a large literals> => (not (is (to_skey x) 'basic')))
        // using the define-fun pattern, since we need to list all largeConstantsInCode here, which might lead to much
        // duplication
        // note that it's not sound to just filter for arg !in largeConstants in code here, because the program
        // might force some identifier that appears under `to_skey` to be equal to one of these constants
        //  --> thus we have to make this big conjunction in the antecedent
        toSkeyNonBasic.addAllToContainer(axiomContainer, toSkeyApps.map { it.args.single() })

        fromSkeyVsBasic.addAllToContainer(axiomContainer, fromSkeyApps.map { it.args.single() })

        // (from_skey (skey_add <skey> <offset>)) = (+ (from_skey <skey>) <offset>)))
        skeyAdditions.forEach { skeyAdd ->
            val (skey, offset) = skeyAdd.args
            axiomContainer.addAxioms(
                "(from_skey (skey_add <skey> <offset>)) = (+ (from_skey <skey>) <offset>)))" to {
                    (applyExp(AxiomatizedFunctionSymbol.SKeyDt.FromSkey(Tag.Bit256), skeyAdd)) eq
                            (applyExp(AxiomatizedFunctionSymbol.SKeyDt.FromSkey(Tag.Bit256), skey) intAdd offset)
                },
            )
        }

        // toSkey(<largeConstantInCode>) = basic(<largeConstantInCode>)
        largeConstantsInCode.forEach { c ->
            axiomContainer.addAxioms(
                "toSkey(<largeConstantInCode>) = basic(<largeConstantInCode>)" to
                        { applyExp(AxiomatizedFunctionSymbol.SKeyDt.ToSkey(Tag.Bit256), litInt(c)) eq basicSkey(litInt(c)) },
                "<largeConstantInCode> = from_skey(basic(<largeConstantInCode>))" to
                        { litInt(c) eq applyExp(AxiomatizedFunctionSymbol.SKeyDt.FromSkey(Tag.Bit256), basicSkey(litInt(c))) }
            )
        }

        super.yield(axiomContainer)
    }

    override fun beforeScriptFreeze() {
        // always have at least one  non-basic constructor, otherwise the succedent of this axiom becomes effectively
        //  `false`, which is not what we want
        // x > max_solidity_slot && <x does not equal one of the a large literals> => (not (is (to_skey x) 'basic')))
        nonBasicDtConstructors.add(AxiomatizedFunctionSymbol.SKeyDt.SkeyNode(1))
        nonBasicDtConstructors.add(AxiomatizedFunctionSymbol.SKeyDt.SkeyNode(2))

        toSkeyNonBasic
        fromSkeyVsBasic

        val dtConstructors = nonBasicDtConstructors + AxiomatizedFunctionSymbol.SKeyDt.Basic(Tag.Int)
        val dtDecl = LExpressionFactory.DatatypeDeclaration(
            sortDecs = listOf(dtSortDecLExp),
            constructorDecListList = listOf(
                dtConstructors.map { fs ->
                    LExpressionFactory.DatatypeDeclaration.ConstructorDec(
                        fs,
                        List((fs.signature as IFixedFunctionSignatures).paramSorts.size) { i ->
                            LExpressionFactory.DatatypeDeclaration.SelectorDec(
                                AxiomatizedFunctionSymbol.SKeyDt.SKeySelector(
                                    fs,
                                    i,
                                    skeySort
                                )
                            )
                        }
                    )
                }
            )
        )
        lxf.registerDatatypeDeclaration(dtDecl)

        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.SKeyDt.Basic(Tag.Bit256))
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.SKeyDt.Basic(Tag.Int))
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.SKeyDt.SkeyAdd(Tag.Bit256))
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.SKeyDt.SkeyAdd(Tag.Int))
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.SKeyDt.ToSkey(Tag.Bit256))
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.SKeyDt.ToSkey(Tag.Int))
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.SKeyDt.FromSkey(Tag.Bit256))
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.SKeyDt.FromSkey(Tag.Int))

        // a bit hacky, but the only way to untangle this, since largeConstantsInCode may be updated through ghost
        // axioms after this (see comment to <symbolsFrozen>), thus we can't initialized the lazy [toSkeyNonBasic] field
        // TODO: this is especially bad due to the string construction here; the define-fun infrastructure probably
        //  should get some tweaks to support this better sometime
        lxf.registerFunctionSymbol(
            AxiomatizedFunctionSymbol.DefFunc(
                "axiom_$toSkeyNonBasicName",
                FixedFunctionSignatures(listOf(Tag.Int), Tag.Bool)
            )
        )
        lxf.registerFunctionSymbol(
            AxiomatizedFunctionSymbol.DefFunc(
                "axiom_$fromSkeyVsBasicName",
                FixedFunctionSignatures(listOf(skeySort), Tag.Bool)
            )
        )


        super.beforeScriptFreeze()

        symbolsFrozen = true
    }


}
