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

import smt.axiomgenerators.fullinstantiation.StorageHashAxiomGeneratorPlainInjectivity
import smt.solverscript.LExpressionFactory
import vc.data.lexpression.ChainedLExpressionTransformer

abstract class HashAxiomGeneratorContainer(
    lxf: LExpressionFactory,
    allGenerators: List<AxiomGenerator>,
    private val storageHashAxiomGenerator: StorageHashAxiomGenerator,
    private val noLargeGapsHashGenerator: StorageHashAxiomGeneratorPlainInjectivity?
) : AxiomGeneratorContainer(lxf, allGenerators) {
    init {
        check(storageHashAxiomGenerator in allGenerators)
        {
            "Error in HashAxiomGeneratorContainer ($this): HashAxiomGenerator ($storageHashAxiomGenerator) must appear in " +
                    "allGenerators ($allGenerators)"
        }
    }

    override val sortOfStorageKeys = storageHashAxiomGenerator.sortOfStorageKeys

    override val postVisitTransformer = storageHashAxiomGenerator.skeyTransformer

    override val postProcessTransformer = ChainedLExpressionTransformer(
        storageHashAxiomGenerator.skeyTransformer,
        super.postProcessTransformer,
        noLargeGapsHashGenerator?.postProcessSkeyTransformer,
        storageHashAxiomGenerator.postProcessSkeyTransformer,
    )
}
