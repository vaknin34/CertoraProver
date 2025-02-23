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

package smt.axiomgenerators

import datastructures.stdcollections.*
import smt.solverscript.LExpressionFactory
import utils.mapToSet
import vc.data.LExpression
import vc.data.LExpressionWithComment

/**
 * The result of the [Generator.yield] operation. (To be precise, a container is passed to the generator, in order to be
 *  filled by the procedure)
 *
 * In contrast to the generator, this is static. No processing happens, then contained elements don't interact anymore
 *  (like e.g. distributivity entries in Generators might)
 */
class AxiomContainer(val lxf: LExpressionFactory) {
    private var axioms: MutableSet<LExpressionWithComment> = mutableSetOf()

    fun addAxiom(lExpressionWithComment: LExpressionWithComment) {
        axioms.add(lExpressionWithComment)
    }

    fun addAxiom(exp: LExpression, description: String? = null) {
        axioms.add(LExpressionWithComment(exp, description))
    }

    fun addAxioms(vararg pairs: Pair<String, LExpressionFactory.() -> LExpression>) {
        for ((description, expr) in pairs) {
            addAxiom(lxf.expr(), description)
        }
    }

    fun addAll(other: AxiomContainer) {
        axioms.addAll(other.axioms)
    }

    fun addAll(set: AxiomSet) {
        axioms.addAll(set.set)
    }

    fun transform(transformer: (LExpression) -> LExpression) {
        axioms = axioms.mapToSet {
            it.mapLExp(transformer)
        }
    }

    fun getAxiomSequence(): Sequence<LExpressionWithComment> {
        return axioms.asSequence()
    }
}
