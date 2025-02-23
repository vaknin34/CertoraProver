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

package smt.solverscript

import datastructures.EnumSet
import datastructures.enumSetOf
import smt.solverscript.functionsymbols.FunctionSymbol
import smt.solverscript.functionsymbols.TheoryFunctionSymbol
import smtlibutils.data.Logic
import smtlibutils.data.LogicFeature
import solver.SolverConfig


/**
 * All the theory features according to [http://smtlib.cs.uiowa.edu/logics.shtml] (partly outdated) and
 * [http://smtlib.cs.uiowa.edu/benchmarks.shtml].
 *
 * NB: the ordering in this enum is important, it needs to follow the ordering in the smt lib logic descriptor strings,
 *  e.g. there is a logic named QF_AUFLIA, therefore quantifiers < arrays < uf < lia.
 */
enum class SmtTheoryFeature(
    private val present: String,
    private val absent: String = "",
    val interpretedFunctions: (FunctionSymbol) -> Boolean = { false },
) {
    Quantifiers("", "QF_"),
    Arrays("A", interpretedFunctions = ::isTheoryOfArraysSymbols),
    UninterpretedFunctions("UF"),
    DataTypes("DT"),
    IntegerLinearArithmetic("LIA", interpretedFunctions = ::isArithmeticSymbol),
    IntegerNonLinearArithmetic("NIA", interpretedFunctions = ::isArithmeticSymbol),
    Bitvectors("BV", interpretedFunctions = ::isBitVectorTheorySymbol)
    ;
    val smtlibAbbreviation: (Boolean) -> String = { if (it) present else absent }

    companion object {
        fun fromLogicFeature(logicFeature: LogicFeature): SmtTheoryFeature = when (logicFeature) {
            LogicFeature.Quantifiers -> Quantifiers
            LogicFeature.Arrays -> Arrays
            LogicFeature.UninterpretedFunctions -> UninterpretedFunctions
            LogicFeature.DataTypes -> DataTypes
            LogicFeature.IntegerLinearArithmetic -> IntegerLinearArithmetic
            LogicFeature.IntegerNonLinearArithmetic -> IntegerNonLinearArithmetic
            LogicFeature.BitVectors -> Bitvectors
            LogicFeature.RealLinearArithmetic,
            LogicFeature.RealNonLinearArithmetic,
            LogicFeature.IntegerAndRealLinearArithmetic,
            LogicFeature.IntegerAndRealNonLinearArithmetic ->
                throw UnsupportedOperationException("unsupported SmtTheoryFeature: $logicFeature")
        }
    }
}

/**
 * @param keyword the name that appears as an argument to the `set-logic` SMT-Lib command
 */
sealed class SmtTheory(
    open val keyword: String,
    open val theoryFeatures: EnumSet<SmtTheoryFeature>,
    open val arithmeticOperations: ArithmeticOperations
) {
    fun toLogic() = Logic.fromString(keyword)

    override fun toString(): String = keyword

    operator fun plus(theoryFeature: SmtTheoryFeature): SmtTheory =
        fromFeatures(this.theoryFeatures + theoryFeature)

    enum class ArithmeticOperations {
        LinearOnly,
        NonLinear,
        BitVector,
        Any
        ;

       fun toSolverConfigArithOps(): solver.ArithmeticOperations {
            return when (this) {
                LinearOnly -> solver.ArithmeticOperations.LinearOnly
                NonLinear -> solver.ArithmeticOperations.NonLinear
                BitVector -> solver.ArithmeticOperations.BitVector
                Any -> solver.ArithmeticOperations.Any
            }
        }
    }

    val isLia get() = arithmeticOperations == ArithmeticOperations.LinearOnly
    val isNia get() = arithmeticOperations == ArithmeticOperations.NonLinear
    val isBv get() = arithmeticOperations == ArithmeticOperations.BitVector
    val isOther get() = arithmeticOperations == ArithmeticOperations.Any
    val arrayTheoryMode get() = SmtTheoryFeature.Arrays in theoryFeatures

    companion object {

        fun fromFeatures(features: EnumSet<SmtTheoryFeature>): SmtTheory = Standard(features)
        fun fromLogic(logic: Logic): SmtTheory =
            fromFeatures(enumSetOf<SmtTheoryFeature>() + logic.logicFeatures.map { SmtTheoryFeature.fromLogicFeature(it) })
        fun fromString(s: String): SmtTheory = fromLogic(Logic.fromString(s))
    }

    class Standard(features: EnumSet<SmtTheoryFeature>) : SmtTheory(
        keyword = SmtTheoryFeature.values().joinToString("") { it.smtlibAbbreviation(it in features) },
        theoryFeatures = features,
        arithmeticOperations = when {
            SmtTheoryFeature.IntegerLinearArithmetic in features -> {
                check(SmtTheoryFeature.IntegerNonLinearArithmetic !in features)
                check(SmtTheoryFeature.Bitvectors !in features)
                ArithmeticOperations.LinearOnly
            }
            SmtTheoryFeature.IntegerNonLinearArithmetic in features -> {
                check(SmtTheoryFeature.IntegerLinearArithmetic !in features)
                check(SmtTheoryFeature.Bitvectors !in features)
                ArithmeticOperations.NonLinear
            }
            SmtTheoryFeature.Bitvectors in features -> {
                check(SmtTheoryFeature.IntegerLinearArithmetic !in features)
                check(SmtTheoryFeature.IntegerNonLinearArithmetic !in features)
                ArithmeticOperations.BitVector
            }
            else -> {
                throw UnsupportedOperationException("no arithmetic operations in smt theory, unexpected")
            }
        }

    )

    object ALL :
        SmtTheory(
            "ALL",
            enumSetOf(
                SmtTheoryFeature.Arrays,
                SmtTheoryFeature.Quantifiers,
                SmtTheoryFeature.UninterpretedFunctions,
                SmtTheoryFeature.IntegerNonLinearArithmetic,
                SmtTheoryFeature.Bitvectors
            ),
            ArithmeticOperations.NonLinear // TODO use Any, once it exists
        )

    fun toSolverConfigLogicFeatures(): SolverConfig.LogicFeatures {
        return SolverConfig.LogicFeatures(
            this.arithmeticOperations.toSolverConfigArithOps(),
            SmtTheoryFeature.DataTypes in this.theoryFeatures,
             SmtTheoryFeature.Quantifiers in this.theoryFeatures
        )
    }
}

private fun isTheoryOfArraysSymbols(fs: FunctionSymbol) = fs is TheoryFunctionSymbol.Array

private fun isArithmeticSymbol(fs: FunctionSymbol) = fs in arithmeticSymbols

private val arithmeticSymbols: Set<TheoryFunctionSymbol> =
    setOf(
        TheoryFunctionSymbol.Unary.Sub,
        TheoryFunctionSymbol.Binary.IntGt,
        TheoryFunctionSymbol.Binary.IntLe,
        TheoryFunctionSymbol.Binary.IntLt,
        TheoryFunctionSymbol.Binary.IntSub,
        TheoryFunctionSymbol.Vec.IntAdd,
        TheoryFunctionSymbol.Vec.IntMul.IntMulAllowNormalize,
        TheoryFunctionSymbol.Vec.IntMul.IntMulDontNormalize,
        TheoryFunctionSymbol.Binary.IntDiv.IntDivDontNormalize,
        TheoryFunctionSymbol.Binary.IntDiv.IntDivAllowNormalize,
        TheoryFunctionSymbol.Binary.IntMod.IntModDontNormalize,
        TheoryFunctionSymbol.Binary.IntMod.IntModAllowNormalize
    )

private fun isBitVectorTheorySymbol(fs: FunctionSymbol) = fs in bitvectorTheorySymbols

private val bitvectorTheorySymbols = setOf(
    TheoryFunctionSymbol.BV.BvNot,
    TheoryFunctionSymbol.BV.BvNeg,
    TheoryFunctionSymbol.BV.BvAdd,
    TheoryFunctionSymbol.BV.BvMul,
    TheoryFunctionSymbol.BV.BvAnd,
    TheoryFunctionSymbol.BV.BvLshr,
    TheoryFunctionSymbol.BV.BvShl,
    TheoryFunctionSymbol.BV.BvUDiv,
    TheoryFunctionSymbol.BV.BvULt,
    TheoryFunctionSymbol.BV.BvURem,
    TheoryFunctionSymbol.BV.BvConcatTwo256s,
    TheoryFunctionSymbol.BV.BvExtractLower256From512,
)


