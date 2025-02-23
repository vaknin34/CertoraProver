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

package smt


/** Can hold many [SmtBackendConfig]s that can be run in parallel. */
//@Deprecated("never worked")
//data class ParallelSmtBackendConfigs(val smtBackendConfigs: List<SmtBackendConfig>) :
//    List<SmtBackendConfig> by smtBackendConfigs {
//    constructor(vararg smtBackendConfigs: SmtBackendConfig) : this(smtBackendConfigs.toList())
//
//
//    companion object {
//        /** TODO .. implemented like this it's a rather dumb strategy -> shouldn't wait for NIA, if LIA says 'unsat' */
//        fun evaluateParallelResults(results: List<Pair<SmtBackendConfig, Verifier.VerifierResult>>): Verifier.VerifierResult {
//            return when (results.size) {
//                1 -> results.first().second
//                2 -> {
//                    val lia =
//                        results.find { it.first.theory.arithmeticOperations == SmtTheory.ArithmeticOperations.LinearOnly }
//                            ?: error("expected to find LIA config")
//                    val nia =
//                        results.find { it.first.theory.arithmeticOperations == SmtTheory.ArithmeticOperations.NonLinear }
//                            ?: error("expected to find NIA config")
//                    val liaRes = lia.second
//                    val niaRes = nia.second
//
//                    when (liaRes.solverResult) {
//                        SolverResult.SAT -> niaRes
//                        SolverResult.UNSAT -> liaRes
//                        SolverResult.UNKNOWN -> niaRes
//                        SolverResult.TIMEOUT -> niaRes
//                    }
//                }
//                else -> error("unexpected number of smt configs")
//            }
//        }
//
//    }
//}
