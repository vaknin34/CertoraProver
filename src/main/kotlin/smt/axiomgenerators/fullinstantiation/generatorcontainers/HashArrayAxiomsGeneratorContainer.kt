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

package smt.axiomgenerators.fullinstantiation.generatorcontainers

import smt.HashingScheme
import smt.axiomgenerators.BvOverflowChecksViaDefineFuns
import smt.axiomgenerators.fullinstantiation.*
import smt.newufliatranslator.AxiomGenerator
import smt.newufliatranslator.HashAxiomGeneratorContainer
import smt.newufliatranslator.StorageHashAxiomGenerator
import smt.solverscript.LExpressionFactory
import smt.solverscript.SmtTheory
import smt.solverscript.SmtTheoryFeature
import vc.data.lexpression.ChainedLExpressionTransformer
import verifier.CreateAxiomGeneratorContainer

/**
 * Should be suitable e.g. for UFBV logic.
 *
 * Generates axioms for array modelling through uninterpreted functions. (and no others)
 *
 * When using some BV logic, this will only work with an [StorageHashAxiomGenerator] different from [HashGenerator].
 */
class HashArrayAxiomsGeneratorContainer private constructor(
    lxf: LExpressionFactory,
    private val arrayGenerator: ArrayGenerator,
    hashGenerator: StorageHashAxiomGenerator,
    noLargeGapsHashGenerator: StorageHashAxiomGeneratorPlainInjectivity?,
    generators: List<AxiomGenerator>,
) : HashAxiomGeneratorContainer(
    lxf,
    generators,
    hashGenerator,
    noLargeGapsHashGenerator,
) {
    init {
        check(hashGenerator in generators)
        check(arrayGenerator in generators)
    }

    override val postProcessTransformer = ChainedLExpressionTransformer(
        super.postProcessTransformer,
        arrayGenerator.postProcessArrayTransformer,
    )

    companion object {
        fun create(
            lxf: LExpressionFactory,
            targetTheory: SmtTheory,
            hashingScheme: HashingScheme,
            overflowChecks: CreateAxiomGeneratorContainer.Config.BvOverflowChecks,
        ): HashArrayAxiomsGeneratorContainer {
            check(
                hashingScheme !is HashingScheme.Legacy ||
                        SmtTheoryFeature.Bitvectors !in targetTheory.theoryFeatures
            ) { "cannot use legacy hashing scheme \"$hashingScheme\" together with BV logic" }

            val (hashGenerator, noLargeGapsHashGenerator) =
                StorageHashAxiomGenerator.fromHashingScheme(lxf, hashingScheme, targetTheory)
            val arrayGenerator = ArrayGenerator(lxf, targetTheory, hashingScheme) {
                hashGenerator.postProcessSkeyTransformer?.invoke(it) ?: it
            }

            val bvOverflowChecksViaDefineFuns: BvOverflowChecksViaDefineFuns? =
                when (overflowChecks) {
                    CreateAxiomGeneratorContainer.Config.BvOverflowChecks.NewSmtLib -> null
                    CreateAxiomGeneratorContainer.Config.BvOverflowChecks.ViaDefineFun ->
                        BvOverflowChecksViaDefineFuns(lxf)
                    CreateAxiomGeneratorContainer.Config.BvOverflowChecks.DontCare -> null
                }


            // note that we're not registering the bitwise generator -- since we're not interested in it's axioms,
            // since we're translating to BV logic -- kind of hacky, better would be to flexiblize ArrayGenerator
            return HashArrayAxiomsGeneratorContainer(
                lxf,
                arrayGenerator,
                hashGenerator,
                noLargeGapsHashGenerator,
                listOfNotNull(
                    noLargeGapsHashGenerator,
                    arrayGenerator,
                    hashGenerator,
                    bvOverflowChecksViaDefineFuns,
                    BVMathAxiomGenerator(lxf),
                ),
            )
        }
    }
}
