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

import smtlibutils.algorithms.TraverseSmt
import solver.SolverConfig
import java.lang.IllegalArgumentException
import java.lang.StringBuilder
import datastructures.stdcollections.*
import datastructures.EnumSet
import datastructures.enumSetOf

/**
 * All the theory features according to [http://smtlib.cs.uiowa.edu/logics.shtml] (partly outdated) and
 * [http://smtlib.cs.uiowa.edu/benchmarks.shtml].
 *
 * NB: the ordering in this enum is important, it needs to follow the ordering in the smt lib logic descriptor strings,
 *  e.g. there is a logic named QF_AUFLIA, therefore quantifiers < arrays < uf < lia.
 *
 * @param present the string that will occur in the logic name if the feature is present
 * @param absent the string that will occur in the logic name if the feature is absent
 */
enum class LogicFeature(val present: String, val absent: String = "") {
    Quantifiers("", "QF_"),
    Arrays("A"),
    UninterpretedFunctions("UF"),
    DataTypes("DT"),
    IntegerLinearArithmetic("LIA"),
    IntegerNonLinearArithmetic("NIA"),
    RealLinearArithmetic("LRA"),
    RealNonLinearArithmetic("NRA"),
    IntegerAndRealLinearArithmetic("LIRA"),
    IntegerAndRealNonLinearArithmetic("NIRA"),
    BitVectors("BV")
    ;

    val smtlibAbbreviation: (Boolean) -> String = { if (it) present else absent }

    companion object {
        // TODO: use the sorts of [fs] in addition?
        fun fromFunctionSymbol(fs: SmtFunctionSymbol): LogicFeature? {
            return when (fs) {
                is SmtUnintpFunctionSymbol -> UninterpretedFunctions
                is SmtIntpFunctionSymbol -> when (fs) {
                    is SmtIntpFunctionSymbol.Core -> null
                    is SmtIntpFunctionSymbol.IRA -> {
                        when (fs.intOrRealParamSort) {
                            Sort.IntSort -> IntegerNonLinearArithmetic
                            Sort.RealSort -> RealNonLinearArithmetic
                            null -> IntegerAndRealNonLinearArithmetic
                            is Sort.Param -> IntegerAndRealNonLinearArithmetic
                            else -> error("unexpected case in LogicFeature.fromFunctionSymbol")
                        }
                    }
                    is SmtIntpFunctionSymbol.Reals -> RealNonLinearArithmetic // not making the linear/nonlinear distinction
                    is SmtIntpFunctionSymbol.Ints -> IntegerNonLinearArithmetic // not making the linear/nonlinear distinction
                    is SmtIntpFunctionSymbol.Array -> Arrays
                    is SmtIntpFunctionSymbol.BV -> BitVectors
                    is SmtIntpFunctionSymbol.DT -> DataTypes
                }
                else -> error("unexpected function symbol")
            }
        }


        fun hasLinearIntArith(features: EnumSet<LogicFeature>): Boolean {
            return features.containsAny(
                enumSetOf(
                    IntegerLinearArithmetic,
                    RealLinearArithmetic,
                    IntegerAndRealLinearArithmetic
                )
            )
        }

        fun hasNonLinearIntArith(features: EnumSet<LogicFeature>): Boolean {
            return features.containsAny(
                enumSetOf(
                    IntegerNonLinearArithmetic,
                    RealNonLinearArithmetic,
                    IntegerAndRealNonLinearArithmetic
                )
            )
        }

        fun hasIntArith(features: EnumSet<LogicFeature>): Boolean {
            return features.containsAny(
                enumSetOf(
                    IntegerLinearArithmetic,
                    IntegerNonLinearArithmetic,
                    IntegerAndRealLinearArithmetic,
                    IntegerAndRealNonLinearArithmetic
                )
            )
        }

        fun hasRealArith(features: EnumSet<LogicFeature>): Boolean {
            return features.containsAny(
                enumSetOf(
                    RealLinearArithmetic,
                    RealNonLinearArithmetic,
                    IntegerAndRealLinearArithmetic,
                    IntegerAndRealNonLinearArithmetic
                )
            )
        }

        fun hasIntAndRealArith(features: EnumSet<LogicFeature>): Boolean {
            return features.containsAny(
                enumSetOf(
                    IntegerAndRealLinearArithmetic,
                    IntegerAndRealNonLinearArithmetic
                )
            )
        }


        fun normalize(features: EnumSet<LogicFeature>): EnumSet<LogicFeature> {
            var ms = features - enumSetOf(
                    RealLinearArithmetic,
                    RealNonLinearArithmetic,
                    IntegerLinearArithmetic,
                    IntegerNonLinearArithmetic,
                    IntegerAndRealLinearArithmetic,
                    IntegerAndRealNonLinearArithmetic
                )
            if (ms == features) return features // No arithmetics present

            val nonlinear =
                features.containsAny(
                    enumSetOf(
                        IntegerNonLinearArithmetic,
                        RealNonLinearArithmetic,
                        IntegerAndRealNonLinearArithmetic
                    )
                )

            val real =
                features.containsAny(
                    enumSetOf(
                        RealLinearArithmetic,
                        RealNonLinearArithmetic,
                        IntegerAndRealLinearArithmetic,
                        IntegerAndRealNonLinearArithmetic
                    )
                )
            val int =
                features.containsAny(
                    enumSetOf(
                        IntegerLinearArithmetic,
                        IntegerNonLinearArithmetic,
                        IntegerAndRealLinearArithmetic,
                        IntegerAndRealNonLinearArithmetic
                    )
                )

            if (!int && !real && !nonlinear) {
                error("should not be possible")
            } else if (!int && !real && nonlinear) {
                error("should not be possible")
            } else if (!int && real && !nonlinear) {
                ms += RealLinearArithmetic
            } else if (!int && real && nonlinear) {
                ms += RealNonLinearArithmetic
            } else if (int && !real && !nonlinear) {
                ms += IntegerLinearArithmetic
            } else if (int && !real && nonlinear) {
                ms += IntegerNonLinearArithmetic
            } else if (int && real && !nonlinear) {
                ms += IntegerAndRealLinearArithmetic
            } else if (int && real && nonlinear) {
                ms += IntegerAndRealNonLinearArithmetic
            }

            if (ms == enumSetOf(Quantifiers)) {
                ms += UninterpretedFunctions
            }
            return ms
        }

        fun fromSort(sort: Sort): EnumSet<LogicFeature> {
            check(!sort.isParametrized()) { "trying to get logic features from an uninstantiated sort -- unexpected" }
            return when (sort) {
                Sort.RealSort -> enumSetOf(RealNonLinearArithmetic)
                Sort.IntSort -> enumSetOf(IntegerNonLinearArithmetic)
                Sort.BV256Sort -> enumSetOf(BitVectors)
                else -> {
                    when {
                        sort.isBitVecSort() -> {
                            enumSetOf(BitVectors)
                        }
                        sort.isArraySort() -> {
                            enumSetOf(Arrays) +
                                (sort as Sort.Apply).params.fold(enumSetOf<LogicFeature>()) { set, element -> set + fromSort(element) }
                        }
                        sort is Sort.Apply -> {
                            sort.params.fold(enumSetOf<LogicFeature>()) { set, element -> set + fromSort(element) }
                        }
                        else -> {
                            enumSetOf()
                        }
                    }
                }
            }
        }
    }
}

fun EnumSet<LogicFeature>.hasIntArith(): Boolean = LogicFeature.hasIntArith(this)
fun EnumSet<LogicFeature>.hasRealArith(): Boolean = LogicFeature.hasRealArith(this)
fun EnumSet<LogicFeature>.hasIntAndRealArith(): Boolean = LogicFeature.hasIntAndRealArith(this)
fun EnumSet<LogicFeature>.hasLinearIntArith(): Boolean = LogicFeature.hasLinearIntArith(this)
fun EnumSet<LogicFeature>.hasNonLinearIntArith(): Boolean = LogicFeature.hasNonLinearIntArith(this)


/**
 * Analogue to [Theory] in [LExpression]-related context (not visible from this package)...
 *
 * @param keyword the name that appears as an argument to the `set-logic` SMT-Lib command
 */
sealed class Logic(
    open val keyword: String,
    open val logicFeatures: EnumSet<LogicFeature>,
    open val arithmeticOperations: ArithmeticOperations
) {


    override fun toString(): String = keyword

    enum class ArithmeticOperations {
        LinearOnly,
        NonLinear,
        BitVector,
        Any,
        None;

        fun toSolverConfigArithOps(): solver.ArithmeticOperations {
            return when (this) {
                LinearOnly -> solver.ArithmeticOperations.LinearOnly
                NonLinear -> solver.ArithmeticOperations.NonLinear
                BitVector -> solver.ArithmeticOperations.BitVector
                Any -> solver.ArithmeticOperations.Any
                None -> solver.ArithmeticOperations.None
            }
        }
    }

    operator fun plus(other: Logic): Logic = fromFeatures(this.logicFeatures + other.logicFeatures)

    operator fun minus(other: Logic): Logic = fromFeatures(this.logicFeatures - other.logicFeatures)

    companion object {
        fun fromFeatures(vararg features: LogicFeature): Logic = fromFeatures(features.fold(enumSetOf<LogicFeature>()) { set, el -> set + el })

        fun fromFeatures(features: EnumSet<LogicFeature>): Logic = when (val normalized = LogicFeature.normalize(features)) {
            enumSetOf<LogicFeature>() -> QF_CORE
            else -> Standard(normalized)
        }

        fun fromString(string: String): Logic {
            if (string == "ALL") return ALL
            val substring = StringBuilder()
            var lastFeatureOrdinal = -1
            var features = enumSetOf<LogicFeature>()
            var quantifierFree = false
            string.forEach { c ->
                substring.append(c)
                val matchingFeature = LogicFeature.values().find { it.smtlibAbbreviation(true) == substring.toString() }
                if (matchingFeature != null) {
                    check(lastFeatureOrdinal < matchingFeature.ordinal) {
                        "not a well-formed smtlib logic string, features are not in the right order"
                    }
                    if (features.isEmpty() && !quantifierFree) {
                        features += LogicFeature.Quantifiers
                    }
                    lastFeatureOrdinal = matchingFeature.ordinal
                    features += matchingFeature
                    substring.clear()
                } else if (substring.toString() == "QF_") {
                    // quantifier free logic
                    check(lastFeatureOrdinal < LogicFeature.Quantifiers.ordinal) {
                        "not a well-formed smtlib logic string, features are not in the right order"
                    }
                    lastFeatureOrdinal = LogicFeature.Quantifiers.ordinal
                    quantifierFree = true
                    substring.clear()
                }
            }
            if (substring.isNotEmpty()) {
                throw IllegalArgumentException("Couldn't associate an SMTLib2 Theory with the string \"$string\".")
            }
            return fromFeatures(features)
        }

        fun fromFormula(f: SmtExp): Logic {
            var requiredFeatures = enumSetOf<LogicFeature>()
            val traverser = object : TraverseSmt() {
                override fun quant(exp: SmtExp.Quant) {
                    exp.boundVars.forEach { requiredFeatures += LogicFeature.fromSort(it.sort) }
                    requiredFeatures += LogicFeature.Quantifiers
                    super.quant(exp)
                }

                override fun apply(exp: SmtExp.Apply) {
                    val logicFeature = LogicFeature.fromFunctionSymbol(exp.fs)
                    if (logicFeature != null) {
                        requiredFeatures += logicFeature
                    }
                    super.apply(exp)
                }

                override fun intLit(exp: SmtExp.IntLiteral) {
                    requiredFeatures += LogicFeature.IntegerNonLinearArithmetic
                    super.intLit(exp)
                }

                override fun bitVecLit(exp: SmtExp.BitvectorLiteral) {
                    requiredFeatures += LogicFeature.BitVectors
                    super.bitVecLit(exp)
                }

            }
            traverser.expr(f)
            return fromFeatures(requiredFeatures)
        }
    }

    object CORE :
        Logic(
            "CORE",
            enumSetOf(LogicFeature.Quantifiers),
            ArithmeticOperations.None
        )

    object QF_CORE :
        Logic(
            "QF_CORE",
            enumSetOf(),
            ArithmeticOperations.None
        )


    object ALL :
        Logic(
            "ALL",
            enumSetOf(
                LogicFeature.Quantifiers,
                LogicFeature.Arrays,
                LogicFeature.UninterpretedFunctions,
                LogicFeature.IntegerNonLinearArithmetic,
                LogicFeature.BitVectors,
                LogicFeature.DataTypes
            ),
            ArithmeticOperations.Any
        )

    /**
     * Represents all logics that follow the standard naming scheme, like QF_AUFDTLIA, etc.
     *
     * Assumes [features] has been normalized using [LogicFeature.normalize].
     */
    data class Standard(val features: EnumSet<LogicFeature>) : Logic(
        keyword = LogicFeature.values().joinToString("") { it.smtlibAbbreviation(it in features) },
        logicFeatures = features,
        arithmeticOperations = when {
            features.hasLinearIntArith() && LogicFeature.BitVectors !in features -> ArithmeticOperations.LinearOnly
            features.hasNonLinearIntArith() && LogicFeature.BitVectors !in features -> ArithmeticOperations.NonLinear
            LogicFeature.BitVectors in features && !features.hasLinearIntArith() && !features.hasNonLinearIntArith() ->
                ArithmeticOperations.BitVector
            LogicFeature.BitVectors !in features && !features.hasLinearIntArith() && !features.hasNonLinearIntArith() ->
                ArithmeticOperations.None
            else -> ArithmeticOperations.Any
        }
    ) {
        init {
            val lira = LogicFeature.IntegerAndRealLinearArithmetic
            val lia = LogicFeature.IntegerLinearArithmetic
            val lra = LogicFeature.RealLinearArithmetic
            val nira = LogicFeature.IntegerAndRealNonLinearArithmetic
            val nia = LogicFeature.IntegerNonLinearArithmetic
            val nra = LogicFeature.RealNonLinearArithmetic
            var ctr = 0
            if (lira in logicFeatures) ctr++
            if (lia in logicFeatures) ctr++
            if (lra in logicFeatures) ctr++
            if (nira in logicFeatures) ctr++
            if (nia in logicFeatures) ctr++
            if (nra in logicFeatures) ctr++
            check(ctr <= 1)
            { "too many arithmetics in logicFeatures: $logicFeatures" }
        }


        override fun toString(): String = keyword
    }

    fun toSolverConfigLogicFeatures(): SolverConfig.LogicFeatures {
        return SolverConfig.LogicFeatures(
            this.arithmeticOperations.toSolverConfigArithOps(),
            LogicFeature.DataTypes in this.logicFeatures,
            LogicFeature.Quantifiers in this.logicFeatures
        )
    }
}

fun String.toLogic() = Logic.fromString(this)

