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

import com.tschuchort.compiletesting.KotlinCompilation
import com.tschuchort.compiletesting.SourceFile
import com.tschuchort.compiletesting.symbolProcessorProviders
import ksp.parser.*
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

class TACPrinterGeneratorTester {

    fun injectInSkeleton(cmdsDecl : String = "", exprDecl: String = "") : KotlinCompilation.Result {
        val code =
            """
        package vc.data
        import kotlin.collections
        class TACExprTag
        sealed class TACSymbol {
            data class Var(val namePrefix: String) : TACSymbol()
        }

        sealed class TACCmd {
            sealed class Simple : TACCmd() {
                $cmdsDecl
                data class S1(val i : TACExpr) : Simple()
            }
        }
        sealed class TACExpr  {
            $exprDecl
            data class E1(val i: TACSymbol.Var) : TACExpr()
        }
        """
        val compilation = KotlinCompilation().apply {
            sources = listOf(SourceFile.kotlin("exprPrinterTest.kt", code))
            symbolProcessorProviders = listOf(TACExprPrinterGeneratorProvider(), TACCmdPrinterGeneratorProvider())
            inheritClassPath = true
            messageOutputStream = System.out
        }
        return compilation.compile()
    }

    val exprsShouldSucceed = """
        sealed class TACExpr  {
        data class Expr1(val base: TACSymbol.Var, val lExp: List<TACExpr>) : TACExpr()
        data class ExprTag(val base: TACSymbol.Var, override val tag: Tag?) : TACExpr()
        }"""




    @Test
    fun debugGeneration() {
        val legitCmd = """
        data class LogCmd(
        val args: List<TACSymbol>,
        val memBaseMap: TACSymbol.Var,
        ) : Simple()
        """
        val result = injectInSkeleton(cmdsDecl = legitCmd)
        println(result.messages)
        Assertions.assertEquals(KotlinCompilation.ExitCode.OK, result.exitCode)
    }


    @Test
    fun debugShouldFailGeneration() {
        val unknownShouldFailCompilation =
            """
            data class Expr1(val base: TACSymbol.Var, val lExp: List<TACExpr>) : TACExpr()
            data class UnknownToPrinter(val i: Int, val b: Boolean)
            data class Expr2(val u: UnknownToPrinter) : TACExpr()
        """
        val result= injectInSkeleton(exprDecl = unknownShouldFailCompilation)
        println(result.messages)
        Assertions.assertEquals(KotlinCompilation.ExitCode.COMPILATION_ERROR, result.exitCode)
    }

    @Test
    fun ambigExpr() {
        val ambiguousExprShouldFail =
            """
            data class AmbigExp(val l: List<TACExpr>, val r: List<TACExpr>) : TACExpr()
            """
        val result = injectInSkeleton(exprDecl = ambiguousExprShouldFail)
        Assertions.assertEquals(KotlinCompilation.ExitCode.COMPILATION_ERROR, result.exitCode)
    }

    @Test
    fun ambiguousCmd() {
        val ambiguousCmdShouldFail =
            """
            data class AmbigCmd(val base: List<TACExpr>, val lExp: List<TACExpr>) : TACCmd.Simple()
        """
        val result = injectInSkeleton(ambiguousCmdShouldFail)
        Assertions.assertEquals(KotlinCompilation.ExitCode.COMPILATION_ERROR, result.exitCode)
    }

}
