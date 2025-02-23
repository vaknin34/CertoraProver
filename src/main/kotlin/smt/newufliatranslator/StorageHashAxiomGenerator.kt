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

package smt.newufliatranslator

import analysis.skeyannotation.SkeyDetection
import datastructures.stdcollections.*
import evm.EVM_MOD_GROUP256
import org.jetbrains.annotations.TestOnly
import smt.GenerateEnv
import smt.HashingScheme
import smt.axiomgenerators.fullinstantiation.*
import smt.solverscript.LExpressionFactory
import smt.solverscript.SmtTheory
import smt.solverscript.functionsymbols.*
import tac.Tag
import utils.*
import vc.data.LExpression
import vc.data.TACBuiltInFunction
import vc.data.lexpression.PlainLExpressionTransformer
import vc.gen.LExpVC
import vc.gen.LExpVCMetaData
import java.math.BigInteger

/**
 * Interface for [AxiomGenerator]s that deal with hashing.
 */
abstract class StorageHashAxiomGenerator(
    protected val lxf: LExpressionFactory,
    protected val maxSoliditySlot: BigInteger,
    val sortOfStorageKeys: Tag,
) : AxiomGenerator() {

    /** See documentation of the field of the same name in [LExpVC]. */
    private lateinit var notLargeConstantsInCode: Set<BigInteger>

    @TestOnly
    fun emptyNotLargeConstantsInCode() {
        notLargeConstantsInCode = emptySet()
    }


    private var largeConstantsInCodeFrozen = false
    private val largeConstantsInCodeMutable: MutableSet<BigInteger> = mutableSetOf()
    private fun registerLargeConstantInCode(c: BigInteger) {
        require(!largeConstantsInCodeFrozen) { "largeConstantsInCode must not be frozen when this is updated" }
        if (c !in notLargeConstantsInCode) {
            largeConstantsInCodeMutable.add(c)
        }
    }

    protected val largeConstantsInCode: Set<BigInteger>
        get() {
            largeConstantsInCodeFrozen = true
            return largeConstantsInCodeMutable
        }

    protected val maxSoliditySlotLExp = lxf.litInt(maxSoliditySlot)

    open val skeyTransformer: PlainLExpressionTransformer? = null
    protected fun skeyToIntTransformer(intTag: Tag) = object : PlainLExpressionTransformer("skeyToInt_$intTag") {

        private fun Tag.toInt() = when (this) {
            TACBuiltInFunction.Hash.skeySort -> intTag
            else -> this
        }

        override fun identifierPre(id: LExpression.Identifier): IntermediateLExp =
            runIf(id.tag == TACBuiltInFunction.Hash.skeySort) {
                //if (!lxf.areConstantsFrozen()) {
                    lxf.changeTypeOfConstantSymbol(id.id, intTag)
                //}
                id.copy(tag = intTag).lift()
            } ?: id.lift()

        override fun applyExprPost(exp: ApplyExpr): IntermediateLExp? =
            when (exp.f) {
                is TheoryFunctionSymbol.Array.Select ->
                    runIf(exp.f.signature.getParamSort(1) == TACBuiltInFunction.Hash.skeySort) {
                        exp.copy(f = TheoryFunctionSymbol.Array.Select(exp.f.mapSort, intTag))
                    }

                is TheoryFunctionSymbol.Array.Store ->
                    runIf(exp.f.signature.getParamSort(1) == TACBuiltInFunction.Hash.skeySort) {
                        exp.copy(f = TheoryFunctionSymbol.Array.Store(exp.f.mapSort, intTag))
                    }

                is NonSMTInterpretedFunctionSymbol.MultiDimArray -> {
                    @Suppress("USELESS_IS_CHECK")
                    check(exp.f.mapType is Tag.GhostMap) {
                        "review this when it becomes possible to have a non-ghost mapType"
                    }
                    null
                }

                is TheoryFunctionSymbol.Binary.Eq ->
                    exp.copy(f = exp.f.copy(tag = exp.f.tag.toInt()))
                is TheoryFunctionSymbol.Ternary.Ite ->
                    exp.copy(f = exp.f.copy(tag = exp.f.tag.toInt()))

                else -> null
            }
    }

    /** The TAC builtin function symbols that are introduced during [SkeyDetection] need to be translated differently
     * according to each [StorageHashAxiomGenerator]/[HashingScheme]. This is done in this function, which is called via
     * [AxiomGeneratorContainer.postProcessTransformFlat]. */
    open val postProcessSkeyTransformer: PlainLExpressionTransformer? = null

    override fun visitVCMetaData(lExpVc: LExpVCMetaData) {
        notLargeConstantsInCode = lExpVc.notLargeConstantsInCode
        // show all terms of interest to the generator as if they were in the VC
        //  See [LeinoWP]`.addTermsOI` for an (currently the only) example where there are terms in terms of interest
        //  that are not necessarily in the VC.
        lExpVc.termsOfInterest?.forEach { visit(it, GenerateEnv()) }
        super.visitVCMetaData(lExpVc)
    }

    override fun visit(e: LExpression, env: GenerateEnv) {
        if (e.isNumericLiteral) {
            val i = e.asConst
            if (i > maxSoliditySlot && i < EVM_MOD_GROUP256) {
                registerLargeConstantInCode(i)
            }
        }
        super.visit(e, env)
    }

    companion object {

        /** For the non datatypes-based StorageHashAxiomGenerators, we know that everything that has an `skey` Tag and
         * that remains at declaration-time (i.e. after all (post-)processing done here and in the other generators)
         * must be unused, since we flip the type of every expression to Int in
         * [StorageHashAxiomGenerator.skeyToIntTransformer]. */
        fun filterSkeyDeclarations(fs: FunctionSymbol): Boolean =
            fs.signature.resultSort != TACBuiltInFunction.Hash.skeySort

        fun fromHashingScheme(
            lxf: LExpressionFactory,
            hashingScheme: HashingScheme,
            targetTheory: SmtTheory
        ): Pair<StorageHashAxiomGenerator, StorageHashAxiomGeneratorPlainInjectivity?> {
            fun noLargeGapsGenerator() = StorageHashAxiomGeneratorPlainInjectivity(
                lxf,
                targetTheory = targetTheory,
                axiomatizeKeccack = false
            )
            return when (hashingScheme) {
                is HashingScheme.Legacy ->
                    StorageHashAxiomGeneratorLegacy(lxf, hashingScheme.gapSize) to noLargeGapsGenerator()

                HashingScheme.PlainInjectivity ->
                    StorageHashAxiomGeneratorPlainInjectivity(
                        lxf,
                        targetTheory = targetTheory,
                        axiomatizeKeccack = true
                    ) to null

                HashingScheme.Datatypes ->
                    StorageHashAxiomGeneratorDataTypes(lxf) to noLargeGapsGenerator()
            }
        }
    }
}
