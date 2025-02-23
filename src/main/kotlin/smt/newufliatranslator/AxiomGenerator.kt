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

import datastructures.stdcollections.*
import log.*
import smt.GenerateEnv
import smt.axiomgenerators.AxiomContainer
import smt.axiomgenerators.DefType
import smt.solverscript.functionsymbols.FunctionSymbol
import statistics.SDFeature
import statistics.data.PrettyPrintableStats
import vc.data.LExpression
import vc.gen.LExpVCMetaData

/**
 * Interface for axiom generators
 */
abstract class AxiomGenerator {

    lateinit var axiomGeneratorContainer: AxiomGeneratorContainer

    fun setContainer(container: AxiomGeneratorContainer) {
        axiomGeneratorContainer = container
    }

    open val stats: PrettyPrintableStats? = null

    /**
     * Give the [AxiomGenerator] a peek at the VC's metadata (not the [LExpression]s of the VC, those go through
     * regular [visit]).
     */
    open fun visitVCMetaData(lExpVc: LExpVCMetaData) {
        /* do nothing by default */
    }

    /** visit expression without visiting its descendants */
    open fun visit(e: LExpression, env: GenerateEnv) {}

    open fun <T> timeIt(what: String, thunk: () -> T): T {
        val logger = Logger(LoggerTypes.TIMES)
        logger.info { "$what start for ${this.javaClass.name}" }
        val start = System.currentTimeMillis()
        val res = thunk()
        val end = System.currentTimeMillis()
        logger.info { "$what end for ${this.javaClass.name}: ${(end - start)} milliseconds" }
        return res
    }

    /**
     * Provide axiom data to [axiomContainer].
     * Exact details of how to provide it are implementation-dependent.
     */
    open fun yield(axiomContainer: AxiomContainer) {
        // by default add nothing
    }

    open fun yieldDefineFuns(): List<DefType> = listOf()

    open fun beforeScriptFreeze() {
        // do nothing by default
    }

    open fun declarationFilter(fs: FunctionSymbol): Boolean = true

    /** An [AxiomGenerator] can record some timings and return them through this method for reporting. */
    open fun getStatsRecorders(queryName: String): List<SDFeature<*>> = listOf()

    /**
     * Terms of interest need to undergo the same transformations as other terms, generally; e.g. we apply the
     * using postProcessing to them and such. However, sometimes they needs special treatment in addition. This is
     * what this method allows.
     *
     * The driving example here is to have ArrayGenerator transform map identifiers (e.g. M123) into their UF
     * counterparts (e.g. slct_M123) so we can query those for the model.
     * */
    open fun transformTermsOfInterest(lExp: LExpression): LExpression = lExp
}
