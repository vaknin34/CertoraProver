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

package smtlibutils.externalsolvers.mathematica

import com.wolfram.jlink.Expr
import com.wolfram.jlink.KernelLink
import com.wolfram.jlink.MathLinkException
import com.wolfram.jlink.MathLinkFactory
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.delay
import kotlinx.coroutines.launch
import smtlibutils.algorithms.CollectQualIds
import smtlibutils.algorithms.TraverseSmt
import smtlibutils.data.SatResult
import smtlibutils.data.SmtExp
import smtlibutils.data.SmtIntpFunctionSymbol
import smtlibutils.data.Sort
import utils.*
import java.math.BigInteger

class MathematicaBridge private constructor(
    val arithmeticIR: ArithmeticIR,
    val booleanSortTreatment : BooleanSortTreatment,
    val timeOutMillis: Long,
    mathematicaKernelPath: String
) :
    TraverseSmt() {

    private var cubeOrClauseCnt = 0
    private val qIdsCollector = CollectQualIds()

    private val ml: KernelLink = try {
        MathLinkFactory.createKernelLink("-linkmode launch -linkname '$mathematicaKernelPath'")
    } catch (e: MathLinkException) {
        error("An error occurred connecting to Mathematica kernel: ${e.message}");
    }

    init {
        ml.discardAnswer();
    }

    companion object {
        const val CUBE_OR_CLAUSE: String = "c"

        /**
         * Returns the [SatResult] of the specified [arithmeticIR].
         */
        suspend fun evaluateArithmeticIR(
            arithmeticIR: ArithmeticIR,
            booleanSortTreatment: BooleanSortTreatment = BooleanSortTreatment.EQUALS_ZERO_AS_FALSE_OTHERWISE_TRUE,
            timeOutMillis: Long = 60000,
            mathematicaKernelPath: String = "${System.getProperty("mathematicaHome")}/mathkernel.exe"
        ): SatResult {
            val sender = MathematicaBridge(
                arithmeticIR,
                booleanSortTreatment,
                timeOutMillis,
                mathematicaKernelPath
            )
            sender.sendArithmeticIR()
            sender.sendSolve()
            val solveResult = sender.getSolveResult()
            val result = when (solveResult.solType) {
                MathematicaSolution.Type.FOUND_SOLUTION -> SatResult.SAT(solveResult.sol.toString())
                MathematicaSolution.Type.NO_SOLUTION -> SatResult.UNSAT
                MathematicaSolution.Type.UNKNOWN -> SatResult.UNKNOWN
            }
            sender.terminate()
            return result
        }
    }

    data class MathematicaSolution(val solType: Type, val sol: Map<SmtExp.QualIdentifier, BigInteger> = mapOf()) {
        enum class Type {
            NO_SOLUTION, UNKNOWN, FOUND_SOLUTION
        }
    }

    enum class BooleanSortTreatment {
        EQUALS_ZERO_AS_FALSE_OTHERWISE_TRUE, USE_BOOLEANS_DOMAIN
    }

    private sealed class MathFunction(open val id: String, open val arity: Int) {
        object EvaluatePacket : MathFunction("EvaluatePacket", 1)
        object Set : MathFunction("Set", 2)
        object SetDelayed : MathFunction("SetDelayed", 2)
        object Plus : MathFunction("Plus", 2)
        object Subtract : MathFunction("Subtract", 2)
        object Times : MathFunction("Times", 2)
        object Divide : MathFunction("Divide", 2)
        object IntegerPart : MathFunction("IntegerPart", 1)
        object Mod : MathFunction("Mod", 2)
        object Minus : MathFunction("Minus", 1)
        object Abs : MathFunction("Abs", 1)
        object Equal : MathFunction("Equal", 2)
        object Unequal : MathFunction("Unequal", 2)
        object LessEqual : MathFunction("LessEqual", 2)
        object Less : MathFunction("Less", 2)
        object And : MathFunction("And", 0)
        object Or : MathFunction("Or", 0)
        object Not : MathFunction("Not",1)

        object Solve : MathFunction("Solve", 3)
        object Reduce : MathFunction("Reduce", 4)
        object FindInstance : MathFunction("FindInstance", 4)
        object List : MathFunction("List", 0)
        object Simplify : MathFunction("Simplify", 1)
        object FromDigits : MathFunction("FromDigits", 1)
        object Rule : MathFunction("Rule", 2)
        object Element : MathFunction("Element", 2)


        companion object {
            fun fromIntSmtFunctionSymbol(fs: SmtIntpFunctionSymbol.Ints): MathFunction = when (fs) {
                SmtIntpFunctionSymbol.Ints.Neg -> Minus
                SmtIntpFunctionSymbol.Ints.Sub -> Subtract
                SmtIntpFunctionSymbol.Ints.Add -> Plus
                SmtIntpFunctionSymbol.Ints.Mul -> Times
                SmtIntpFunctionSymbol.Ints.Div -> Divide
                SmtIntpFunctionSymbol.Ints.Mod -> Mod
                SmtIntpFunctionSymbol.Ints.Abs -> Abs
            }
        }
    }

    private sealed class MathSymbol(val id: String) {
        object Integers : MathSymbol("Integers")
        object Reals : MathSymbol("Reals")
        object Booleans : MathSymbol("Booleans")
    }

    private fun put(mathFs: MathFunction, argCount: Int = mathFs.arity) = apply {
        ml.putFunction(mathFs.id, argCount)
    }

    private fun put(mathSym: MathSymbol) = apply { put(mathSym.id) }

    private fun put(boolLit : Boolean) = apply { ml.put(boolLit) }

    private fun put(symbol: String) = apply { ml.putSymbol(symbol) }

    private fun put(bigInt: BigInteger) = apply {
        put(MathFunction.FromDigits)
        ml.put(bigInt.toString(10))
    }

    private fun put(symbolArgs: Collection<String>, mathFs: MathFunction = MathFunction.List) = apply {
        put(mathFs, symbolArgs.count())
        symbolArgs.forEach { put(it) }
    }

    private fun nextCubeOrClauseId(): String = "$CUBE_OR_CLAUSE${cubeOrClauseCnt++}"

    private fun cubeOrClauseIdsList(): List<String> {
        var idx = 0
        return generateSequence { if (idx < cubeOrClauseCnt) "$CUBE_OR_CLAUSE${idx++}" else null }.toList()
    }

    private suspend fun endSend(discardAnswer: Boolean = false) = coroutineScope {
        ml.endPacket()

        val timeOutJob = launch {
            delay(timeOutMillis) //wait the timeout period
            //ml.abortEvaluation() //timeout has occurred
            ml.abandonEvaluation()
        }

        launch {
            try {
                if (discardAnswer) {
                    ml.discardAnswer()
                } else {
                    ml.waitForAnswer()
                }
            } catch (e: MathLinkException) {
                if(!ml.clearError()) {
                    ml.terminateKernel()
                }
            }
            if (timeOutJob.isActive) {
                //An answer has been obtained before timeout
                timeOutJob.cancel()
            }
        }
    }

    private suspend fun sendArithmeticIR() = arithmeticIR.constraints.forEach { send(it) }

    private suspend fun send(cubeOrClause: Set<ArithmeticIR.Constraint>) {
        check(cubeOrClause.isNotEmpty())
        try {
            //Send: c_i = AND/OR(lhs ? rhs)
            put(MathFunction.EvaluatePacket).put(
                MathFunction.SetDelayed
            ).put(nextCubeOrClauseId())
            if (cubeOrClause.count() > 1) {
                when (arithmeticIR.mode) {
                    ArithmeticIR.Mode.CNF -> put(MathFunction.Or, cubeOrClause.count())
                    ArithmeticIR.Mode.DNF -> put(MathFunction.And, cubeOrClause.count())
                }
            }
            cubeOrClause.forEach { send(it) }
            endSend(true)
        } catch (e: MathLinkException) {
            ml.close()
            error("MathLinkException occurred: " + e.message)
        }
    }

    private fun send(ac: ArithmeticIR.Constraint) {
        when (ac) {
            is ArithmeticIR.Constraint.Equation -> {
                when (ac.polarity) {
                    true -> put(MathFunction.Unequal)
                    false -> put(MathFunction.Equal)
                }
            }
            is ArithmeticIR.Constraint.InEquation -> {
                when (ac.isStrict) {
                    true -> put(MathFunction.Less) // <
                    false -> put(MathFunction.LessEqual) // <=
                }
            }
            is ArithmeticIR.Constraint.BooleanVariable -> {
                check(!ac.rhs.b)
                if (booleanSortTreatment == BooleanSortTreatment.USE_BOOLEANS_DOMAIN) {
                    put(MathFunction.And, 2)
                    put(MathFunction.Element)
                    put(ac.lhs.id.sym)
                    put(MathSymbol.Booleans)
                }
                when (ac.polarity) {
                    true -> put(MathFunction.Equal)
                    false -> put(MathFunction.Unequal)
                }
            }
        }

        //send lhs
        expr(ac.lhs)
        //send rhs
        expr(ac.rhs)

        //collect (free) variables' names
        qIdsCollector.process(ac.lhs)
        qIdsCollector.process(ac.rhs)
    }

    suspend fun sendSolve() {
        check(cubeOrClauseCnt > 0) { "There are no arithmetic constraints to solve" }
        try {
            put(MathFunction.EvaluatePacket).put(
                MathFunction.FindInstance
            )
            val cIdsList = cubeOrClauseIdsList()
            when (arithmeticIR.mode) {
                ArithmeticIR.Mode.CNF -> {
                    if (cIdsList.count() == 1) put(cIdsList[0]) else put(cIdsList,
                        MathFunction.And
                    )
                }
                ArithmeticIR.Mode.DNF -> {
                    if (cIdsList.count() == 1) put(cIdsList[0]) else put(cIdsList,
                        MathFunction.Or
                    )
                }
            }
            /*if (arithmeticIR.qualIdSanitizer.sanitizedIdToOrigQualId.count() == 1) {
                put(arithmeticIR.qualIdSanitizer.sanitizedIdToOrigQualId.keys.first())
            } else {
                put(arithmeticIR.qualIdSanitizer.sanitizedIdToOrigQualId.keys)
            }*/
            if (qIdsCollector.result.count() == 1) {
                put(qIdsCollector.result.first().id.sym)
            } else {
                put(qIdsCollector.result.map { it.id.sym })
            }
            put(MathSymbol.Integers) //Find solutions over the Integers domain
            put(BigInteger.ONE) //Retrieve at most one solution/model
            endSend()
        } catch (e: MathLinkException) {
            ml.close()
            error("MathLinkException occurred: " + e.message)
        }
    }

    private fun extractMathematicaModel(qListExpr: Expr): Map<SmtExp.QualIdentifier, BigInteger> {
        val res = mutableMapOf<SmtExp.QualIdentifier, BigInteger>()
        qListExpr.args().forEach { mathematicaRulesList ->
            check(mathematicaRulesList.listQ())
            check(mathematicaRulesList.length() > 0)
            mathematicaRulesList.args().forEach { rule ->
                check(rule.length() == 2)
                check(rule.args()[0].symbolQ())
                check(rule.args()[1].integerQ() || rule.args()[1].symbolQ())
                val qualId = arithmeticIR.qualIdSanitizer.sanitizedIdToOrigQualId.getValue(rule.args()[0].asString())
                res[qualId] = when (qualId.sort) {
                    Sort.IntSort -> rule.args()[1].asBigInteger()
                    Sort.BoolSort -> {
                        if(booleanSortTreatment == BooleanSortTreatment.EQUALS_ZERO_AS_FALSE_OTHERWISE_TRUE) {
                            when(rule.args()[1].asBigInteger()) {
                                BigInteger.ZERO -> BigInteger.ZERO
                                else -> BigInteger.ONE
                            }
                        } else {
                            when(rule.args()[1].asString()!!.toBoolean()) {
                                true -> BigInteger.ONE
                                false -> BigInteger.ZERO

                            }
                        }
                    }
                    else -> error("The qualifierId $qualId has the unexpected sort ${qualId.sort}")
                }
            }
        }
        return res
    }

    private fun getSolveResult(): MathematicaSolution {
        val expr = ml.expr
        ml.newPacket()
        if (expr.listQ()) {
            return if (expr != Expr(Expr(Expr.SYMBOL, MathFunction.List.id), arrayOf())) {
                MathematicaSolution(
                    MathematicaSolution.Type.FOUND_SOLUTION,
                    extractMathematicaModel(expr)
                )
            } else {
                MathematicaSolution(
                    MathematicaSolution.Type.NO_SOLUTION
                )
            }
        }
        return MathematicaSolution(
            MathematicaSolution.Type.UNKNOWN
        )
    }

    fun terminate() {
        ml.close()
    }

    override fun apply(exp: SmtExp.Apply) {
        check(exp.fs is SmtIntpFunctionSymbol.Ints) { "All function symbols must be SmtIntpFunctionSymbol.Ints; found ${exp.fs}" }
        if(exp.fs == SmtIntpFunctionSymbol.Ints.Div) {
            put(MathFunction.IntegerPart)
        }
        put(
            MathFunction.fromIntSmtFunctionSymbol(
                exp.fs as SmtIntpFunctionSymbol.Ints
            ), exp.args.count())
        exp.args.forEach { expr(it) }
    }

    override fun qualId(exp: SmtExp.QualIdentifier) {
        put(exp.id.sym)
    }

    override fun boolLit(exp: SmtExp.BoolLiteral) {
        when (booleanSortTreatment) {
            BooleanSortTreatment.EQUALS_ZERO_AS_FALSE_OTHERWISE_TRUE -> {
                when (exp.b) {
                    false -> put(BigInteger.ZERO)
                    true -> error("Did not expect a True literal")
                }
            }
            BooleanSortTreatment.USE_BOOLEANS_DOMAIN -> put(exp.b)
        }
    }

    override fun bitVecLit(exp: SmtExp.BitvectorLiteral) = error("expected an expression of sort Int")

    override fun intLit(exp: SmtExp.IntLiteral) {
        put(exp.i)
    }

    override fun forallExp(exp: SmtExp.Quant.ForAll) = error("expected an expression of sort Int")

    override fun existsExp(exp: SmtExp.Quant.Exists) = error("expected an expression of sort Int")

    override fun lambda(exp: SmtExp.Lambda) = error("expected an expression of sort Int")

    override fun letExp(exp: SmtExp.Let) = error("expected an expression of sort Int")
}

