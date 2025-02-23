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
import smt.axiomgenerators.fullinstantiation.BVMathAxiomGenerator
import smt.axiomgenerators.fullinstantiation.StorageHashAxiomGeneratorPlainInjectivity
import smt.newufliatranslator.AxiomGenerator
import smt.newufliatranslator.AxiomGeneratorContainer
import smt.newufliatranslator.HashAxiomGeneratorContainer
import smt.newufliatranslator.StorageHashAxiomGenerator
import smt.solverscript.LExpressionFactory
import smt.solverscript.SmtTheory
import smt.solverscript.SmtTheoryFeature
import verifier.CreateAxiomGeneratorContainer

/**
 * Should be suitable e.g. for AUFBV logic.
 *
 * This will only work with [HashingScheme]s that are compatible to BV logics.
 */
class HashOnlyGeneratorContainer private constructor(
    lExprFact: LExpressionFactory,
    storageHashAxiomGenerator: StorageHashAxiomGenerator,
    noLargeGapsHashGenerator: StorageHashAxiomGeneratorPlainInjectivity?,
    generators: List<AxiomGenerator>,
) : HashAxiomGeneratorContainer(
    lExprFact,
    generators,
    storageHashAxiomGenerator,
    noLargeGapsHashGenerator
) {

    companion object {
        fun create(
            lxf: LExpressionFactory,
            targetTheory: SmtTheory,
            hashingScheme: HashingScheme,
            overflowChecks: CreateAxiomGeneratorContainer.Config.BvOverflowChecks,
        ): AxiomGeneratorContainer {
            check(
                hashingScheme !is HashingScheme.Legacy ||
                        SmtTheoryFeature.Bitvectors !in targetTheory.theoryFeatures
            ) { "cannot use legacy hashing scheme \"${hashingScheme}\" together with BV logic" }

            val (hashGenerator, noLargeGapsHashGenerator) =
                StorageHashAxiomGenerator.fromHashingScheme(lxf, hashingScheme, targetTheory)

            val bvOverflowChecksViaDefineFuns: BvOverflowChecksViaDefineFuns? =
                when (overflowChecks) {
                    CreateAxiomGeneratorContainer.Config.BvOverflowChecks.NewSmtLib -> null
                    CreateAxiomGeneratorContainer.Config.BvOverflowChecks.ViaDefineFun ->
                        BvOverflowChecksViaDefineFuns(lxf)
                    CreateAxiomGeneratorContainer.Config.BvOverflowChecks.DontCare -> null
                }

            return HashOnlyGeneratorContainer(
                lxf,
                hashGenerator,
                noLargeGapsHashGenerator,
                listOfNotNull(
                    noLargeGapsHashGenerator,
                    hashGenerator,
                    bvOverflowChecksViaDefineFuns,
                    BVMathAxiomGenerator(lxf)
                ),
            )

        }
    }
}
