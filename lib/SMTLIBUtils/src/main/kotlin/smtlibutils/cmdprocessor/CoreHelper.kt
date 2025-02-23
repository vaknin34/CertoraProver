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

package smtlibutils.cmdprocessor

import datastructures.Bijection
import datastructures.stdcollections.*
import log.*
import smtlibutils.data.HasSmtExp
import smtlibutils.data.ISmtScript
import smtlibutils.data.SmtExp


private val logger = Logger(SMTLIBUtilsLoggerTypes.SMTLIBUTILS)

/**
 * The [CoreHelper] takes care of some technical details when preparing a formula for  unsat- or timeout-core generation
 * and parsing back of the [unsat|timeout] core from the solver:
 * - generating unique names for the assertions
 * - annotating assertions with these names
 * - parsing the output of the get-[unsat|timeout]-core command
 * - mapping between original assertions, annotated assertions and their names
 */
class CoreHelper(assertions: List<HasSmtExp>, script: ISmtScript) {

    /** Bijective map between names and original (not annotated) smt expressions */
    val nameToOriginal: Bijection<String, HasSmtExp> = Bijection.fromPairs(
        // make sure the name matches what we parse in [parseUnsatCore]
        assertions.mapIndexed { id, exp -> "ucn${id}" to exp }
    )

    /** Maps names to annotated smt expressions */
    val nameToAnnotated: Map<String, HasSmtExp> = nameToOriginal.mapValues { (key, value) ->
        value.mapExp { script.annotatedExp(value.exp, script.namedAnnotation(key)) }
    }

    /** the unsat core is given as a list of names referring to [nameToOriginal] and [nameToAnnotated]. */
    lateinit var core: Set<String>

    /**
     * Parses the core from the solver output and stores it into [core].
     * The solver output is expected to have the format `(ucn<i1> ucn<i2> ...)`, and we store the names in
     * [core], which can then be used as keys for [nameToOriginal] or [nameToAnnotated].
     */
    @Suppress("ForbiddenMethodCall")
    fun parseCore(solverOutput: List<String>) {
        val line = solverOutput.joinToString(" ")
        // make sure the pattern matches what we create in [nameToOriginal]
        core = Regex("ucn\\d+").findAll(line).map { it.value }.toSet()
        core.forEach { check(nameToOriginal.containsKey(it)) }
    }

    /** Get all annotated terms. */
    fun getAnnotated(): Collection<HasSmtExp> = nameToAnnotated.values

    val coreAsHasSmtExps: List<HasSmtExp> get() = core.mapNotNull {
        val res = nameToOriginal[it]
        if (res == null) { logger.warn { "core helper internal mapping `nameToOriginal` is incomplete on \"$it\"" } }
        res
    }

    /** Get all assertions from the original formula that are part of the unsat-/timeout-core. */
    val coreAsSmtExps: List<SmtExp> get() = coreAsHasSmtExps.map { it.exp }
}
