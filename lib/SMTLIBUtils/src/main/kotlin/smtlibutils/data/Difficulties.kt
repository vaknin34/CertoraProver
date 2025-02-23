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

package smtlibutils.data

import log.*
import smtlibutils.cmdprocessor.SmtFormulaCheckerResult
import smtlibutils.parser.SMTParser
import java.math.BigInteger

/**
 * Wraps the results of a "(get-difficulty)" query to the solver (only supported by an experimental CVC5 branch right
 * now).
 */
sealed class Difficulties {
    data class Single(val expToDifficulty: Map<SmtExp, BigInteger>) : Difficulties()
    companion object {
        fun parse(lines: List<String>): Single {
            val parsed = SMTParser.parseValues(lines.joinToString("\n"), FactorySmtScript)
            val convertedToBigInts: Map<SmtExp, BigInteger> = parsed.entries.mapNotNull { (assertionName, value) ->
                (value as? SmtExp.IntLiteral)?.let { v -> assertionName to v.i }
            }.toMap()
            if (convertedToBigInts.size != parsed.size) {
                logger.info {
                    "lost some values when parsing (get-difficulty) output -- are there non Int-literal " +
                            "values??\n output was: $parsed"
                }
            }
            return Single(convertedToBigInts)
        }
    }
}

/**
 * Contains [Difficulties]-information for one assertion (in the SMTLib meaning of the word, i.e. top-level conjunct)
 * in the VC. Applies only to Leino-style encoding for now (OK-variables get special treatment).
 */
sealed class AssertionDifficulty {
    abstract val assertion: SmtExp
    abstract val assertionComment: String?
    abstract val difficulty: BigInteger

    data class OkVariableDefinition(
        override val assertion: SmtExp,
        override val assertionComment: String?,
        val blockName: String,
        override val difficulty: BigInteger,
    ) : AssertionDifficulty() {
        override fun toString(): String {
            return "OK_$blockName : $difficulty"
        }
    }

    data class AssertionWithComment(
        override val assertion: SmtExp,
        override val assertionComment: String,
        override val difficulty: BigInteger,
    ) : AssertionDifficulty() {
        override fun toString(): String {
            return "Axiom_(${assertionComment}) : $difficulty" // are these always axioms??
        }
    }

    data class Other(
        override val assertion: SmtExp,
        override val assertionComment: String?,
        override val difficulty: BigInteger,
    ) : AssertionDifficulty() {
        override fun toString(): String {
            return "$assertion : $difficulty"
        }
    }
}

data class ProcessDifficultiesResult(val assertionDifficulties: List<AssertionDifficulty>) {
    /** Can be used for identifying the split. */
    fun getOccurringBlocks(): List<String> =
        assertionDifficulties.filterIsInstance<AssertionDifficulty.OkVariableDefinition>().map { it.blockName }

    fun minDifficulty(): BigInteger? {
        return assertionDifficulties.minByOrNull { it.difficulty }?.difficulty
    }

    fun maxDifficulty(): BigInteger? {
        return assertionDifficulties.maxByOrNull { it.difficulty }?.difficulty
    }

    fun getBlockDifficulty(nodeId: String): BigInteger? {
        return assertionDifficulties
            .find { it is AssertionDifficulty.OkVariableDefinition && it.blockName == nodeId }
            ?.difficulty
    }
}

object ProcessDifficulties {

    /**
     * Extract a result with difficulties from an [smtFormulaCheckerResult] (if there is any). Parse the
     * assertions a bit and wrap them in [AssertionDifficulty] representation. For further consumption in our reporting
     * infrastructure.
     */
    fun processSmtFormulaCheckerResult(smtFormulaCheckerResult: SmtFormulaCheckerResult): ProcessDifficultiesResult? {
        val resToDifficulties: List<Pair<SmtFormulaCheckerResult.Single, Difficulties>> =
            smtFormulaCheckerResult.getSubresultsWithDifficulties().map {
                it to (((it.satResult as SatResult.UNKNOWN).difficulties)
                    ?: error("getSubresultsWithDifficulties() method should have made sure this is non-null."))
            }
        logger.debug { "getSubresultsWithDifficulties gave $resToDifficulties" }
        val res = if (resToDifficulties.isNotEmpty()) {
            val (res, diff) = resToDifficulties.first()
            val ucHelper = res.unsatCore
            check(ucHelper != null)
            { " Expecting unsat core helper to be present in a result that has difficulties ($res)." }
            check(diff is Difficulties.Single)
            { "Expecting a result that has difficulties to be a `Single` result ($res)." }

            val nameToDifficulty: Map<String, BigInteger> =
                diff.expToDifficulty.mapKeys { (assertionName, _) -> (assertionName as SmtExp.QualIdentifier).id.sym }

            val assertionDifficulties: List<AssertionDifficulty> =
                ucHelper.nameToOriginal.map { (assertionName: String, assertion: HasSmtExp) -> // (index, entry) ->
                    // assertions that aren't mentioned implicitly have difficulty 0
                    val difficulty = nameToDifficulty[assertionName] ?: BigInteger.ZERO
                    when (assertion) {
                        is SmtExpWithComment -> {
                            if (assertion.comment != null) {
                                AssertionDifficulty.AssertionWithComment(
                                    assertion.exp,
                                    assertion.comment,
                                    difficulty
                                )
                            } else {
                                when (val exp = assertion.exp) {
                                    is SmtExp.Apply -> when (exp.fs) {
                                        is SmtIntpFunctionSymbol.Core.Eq -> {
                                            when (val lhs = exp.args[0]) {
                                                is SmtExp.QualIdentifier -> {
                                                    if (lhs.qualification == null && lhs.id.sym.startsWith("OK_")) {
                                                        val suffix = lhs.id.sym.substringAfter("OK_")
                                                        // assertions that aren't mentioned implicitly have difficulty 0
                                                        AssertionDifficulty.OkVariableDefinition(
                                                            exp,
                                                            assertion.comment,
                                                            suffix,
                                                            difficulty,
                                                        )
                                                    } else {
                                                        AssertionDifficulty.Other(
                                                            assertion.exp,
                                                            assertion.comment,
                                                            difficulty
                                                        )
                                                    }
                                                }
                                                else -> {
                                                    AssertionDifficulty.Other(
                                                        assertion.exp,
                                                        assertion.comment,
                                                        difficulty
                                                    )
                                                }
                                            }
                                        }
                                        else -> {
                                            AssertionDifficulty.Other(
                                                assertion.exp,
                                                assertion.comment,
                                                difficulty
                                            )
                                        }
                                    }
                                    else -> {
                                        AssertionDifficulty.Other(assertion.exp, assertion.comment, difficulty)
                                    }
                                }
                            }
                        }
                        else -> AssertionDifficulty.Other(assertion.exp, null, difficulty)
                    }
                }
            ProcessDifficultiesResult(assertionDifficulties)
        } else {
            null
        }
        logger.debug { "from SmtFormulaCheckerResult ($smtFormulaCheckerResult) extracted difficulties ($res)." }
        return res
    }
}


private val logger = Logger(SMTLIBUtilsLoggerTypes.SMTLIBUTILS)
