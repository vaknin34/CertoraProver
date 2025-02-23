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

import com.tschuchort.compiletesting.*
import ksp.parser.TACParserGeneratorProvider
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import java.io.File


class TACParserGeneratorTest {

    /**
     * checks that an unknown argument doesn't compile without either implementing a custom parsing method or annotating
     * the class with @customParser annotation
     */
    @Test
    fun testParserForCustomCode() {
        val shouldNotGenerate = """
            package vc.data
            class MetaMap
            class TACSymbolTable
            sealed class TACCmd {
                abstract val meta: MetaMap
                sealed class Simple : TACCmd() {
                    data class UnknownForParser(val i:Int) //this class doesn't have auto generated parser in TAC when used as an argument in TACCmd
                    data class NotNothingCmd(val u: UnknownForParser, override val meta: MetaMap) : TACCmd.Simple() {
                    }
                }
            }
        """
        val emptyImplementation = """
            package vc.data.parser
            import vc.data.*
            class TACCmdParserImplementation(symbolTable: TACSymbolTable, mapOfMetaMap: Map<Int,MetaMap>) : AbstractTACParserCmd(symbolTable, mapOfMetaMap) {
            //doesn't implements abstract methods.
            }
        """.trimIndent()

        // Configure the test compilation
        val compilation = KotlinCompilation().apply {
            sources = listOf(SourceFile.kotlin("CmdsParsingTest.kt", shouldNotGenerate))
            symbolProcessorProviders = listOf(TACParserGeneratorProvider())
            inheritClassPath = true
        }
        // Run the compilation and get the result
        val result = compilation.compile()
        // Access the KSP-generated files in the output directory
        val kspGeneratedFiles = File(result.outputDirectory.parent, "ksp/sources")
            .walk()
            .filter { it.isFile }
            .toList()
        val compilation2ndRound = KotlinCompilation().apply {
            inheritClassPath = true
            sources = listOf(SourceFile.fromPath(kspGeneratedFiles.first().let{File(it.toURI())}),
                SourceFile.kotlin("CmdsParsingTest.kt", shouldNotGenerate), SourceFile.kotlin("EmptyParserImplementation.kt", emptyImplementation))
        }

        val result2= compilation2ndRound.compile()
        // Check if the compilation was successful
        assertEquals(KotlinCompilation.ExitCode.COMPILATION_ERROR, result2.exitCode, "KSP processing should fail with non-auto generated arg")
        assert(result2.messages.contains("Class 'TACCmdParserImplementation' is not abstract and does not implement abstract base class member"))
    }
}
