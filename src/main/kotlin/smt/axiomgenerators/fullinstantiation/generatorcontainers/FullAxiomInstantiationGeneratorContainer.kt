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
import smt.axiomgenerators.TypeBoundsGenerator
import smt.axiomgenerators.fullinstantiation.*
import smt.newufliatranslator.AxiomGenerator
import smt.newufliatranslator.HashAxiomGeneratorContainer
import smt.newufliatranslator.StorageHashAxiomGenerator
import smt.solverscript.LExpressionFactory
import smt.solverscript.SmtTheory
import vc.data.LExpression
import vc.data.lexpression.ChainedLExpressionTransformer

/**
 * Generates axioms for bitwise operations, nonlinear math, and hashing.
 * For translating to AUFLIA and UFLIA.
 */
class FullAxiomInstantiationGeneratorContainer private constructor(
    lxf: LExpressionFactory,
    hashGenerator: StorageHashAxiomGenerator,
    noLargeGapsHashGenerator: StorageHashAxiomGeneratorPlainInjectivity?,
    private val arrayGenerator: ArrayGenerator,
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

    companion object {

        fun create(
            lxf: LExpressionFactory,
            targetTheory: SmtTheory,
            hashingScheme: HashingScheme,
            linearizationSelector: (LExpression) -> Boolean = { true },
        ): FullAxiomInstantiationGeneratorContainer {
            val mathGenerator = LinearMathAxiomGenerator(lxf, linearizationSelector)
            val bitwiseGenerator = BitwiseAxiomGenerator(lxf, targetTheory, mathGenerator)
            val intMathAxiomGenerator = IntMathAxiomGenerator(lxf, mathGenerator)
            val (hashGenerator, noLargeGapsHashGenerator) =
                StorageHashAxiomGenerator.fromHashingScheme(lxf, hashingScheme, targetTheory)
            val arrayGenerator = ArrayGenerator(lxf, targetTheory, hashingScheme) {
                hashGenerator.postProcessSkeyTransformer?.invoke(it) ?: it
            }
            val typeBasedAxiomsForConstantsGenerator = TypeBoundsGenerator(lxf, targetTheory)

            return FullAxiomInstantiationGeneratorContainer(
                lxf,
                hashGenerator,
                noLargeGapsHashGenerator,
                arrayGenerator,
                listOfNotNull(
                    noLargeGapsHashGenerator,
                    hashGenerator,
                    arrayGenerator,
                    bitwiseGenerator,
                    intMathAxiomGenerator,
                    mathGenerator,
                    typeBasedAxiomsForConstantsGenerator,
                ),
            )
        }
    }

    override val postProcessTransformer = ChainedLExpressionTransformer(
        super.postProcessTransformer,
        arrayGenerator.postProcessArrayTransformer,
    )
}
