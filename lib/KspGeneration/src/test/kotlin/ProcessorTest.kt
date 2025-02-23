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


import ksp.remapper.RemapperProcessor
import ksp.remapper.RemapperProvider
import com.tschuchort.compiletesting.KotlinCompilation
import com.tschuchort.compiletesting.SourceFile
import com.tschuchort.compiletesting.symbolProcessorProviders
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test


class ProcessorTest {

    companion object {
        private const val generateAnnot = "@allocator.GeneratedBy(allocator.Allocator.Id.DUMMY1)"
        private const val uniqueIntf = "${RemapperProcessor.mapperPackage}.${RemapperProcessor.uniqSimpleName}"
        private const val remapperIntf = "${RemapperProcessor.mapperPackage}.${RemapperProcessor.remapperName}"

        private const val generateRemapper = "@allocator.GenerateRemapper"

        private const val metaKey = "tac.MetaKey<Int>"
        private const val badGenerateAnnot = "cannot be marked with @GeneratedBy"

        private const val testClass = "Foo"
        private const val annotatedDecl =  "data class $testClass($generateAnnot val id: Int) : $uniqueIntf"
    }

    private val commonSource = listOf(SourceFile.kotlin("Stub.kt", """
          package allocator

          @Target(AnnotationTarget.CLASS)
          annotation class GenerateRemapper

          @Target(AnnotationTarget.CLASS)
          annotation class GenerateMetaMapper


          @Target(AnnotationTarget.FIELD)
          @Retention(AnnotationRetention.RUNTIME)
          annotation class GeneratedBy(val by: Allocator.Id, val source: Boolean = false)


          object Allocator {
              enum class Id {
                 DUMMY1,
                 DUMMY2;
              }
          }
    """.trimIndent()), SourceFile.kotlin("RemapperEntity.kt", """
        package ${RemapperProcessor.mapperPackage}

        interface ${RemapperProcessor.remapperName} : ${RemapperProcessor.uniqIdName}
    """.trimIndent()), SourceFile.kotlin("UniqueIdEntity.kt", """
        package ${RemapperProcessor.mapperPackage}

        interface ${RemapperProcessor.uniqSimpleName}
    """.trimIndent()), SourceFile.kotlin("MetaKey.kt", """
        package tac

        data class MetaKey<T>(val dummy: Int)
    """.trimIndent()))

    @Test
    fun testWrongGeneratedType() {
        compileWithFail(badGenerateAnnot) { """
            data class Yeet($generateAnnot val foo: String)
        """
        }
    }

    private fun compileSuccess(gen: () -> String) {
        val (_, res) = compile(gen)
        Assertions.assertEquals(KotlinCompilation.ExitCode.OK, res.exitCode)
    }

    private fun compileWithFail(msgFrag: String, gen: () -> String) {
        val (_, res) = compile(gen)
        Assertions.assertEquals(KotlinCompilation.ExitCode.COMPILATION_ERROR, res.exitCode)
        Assertions.assertTrue(res.messages.contains(msgFrag))
    }

    private fun compile(s: () -> String) : Pair<KotlinCompilation, KotlinCompilation.Result> {
        val kComp = KotlinCompilation().apply {
            sources = listOf(
                SourceFile.kotlin(
                    "Yeet.kt", """
                package test

                ${s()}
            """.trimIndent()
                )
            ) + commonSource

            symbolProcessorProviders = listOf(RemapperProvider())
        }
        return kComp to kComp.compile()
    }

    @Test
    fun testRemapperWithoutGenerate() {
        compileWithFail("no corresponding @GenerateRemapper annotation was found") {
            """
                data class Foo($generateAnnot val id: Int) : $remapperIntf
            """.trimIndent()
        }
    }

    @Test
    fun testMissingDirectRemapper() {
        compileWithFail("appears remappable, but this class is not") {
            """
                data class Foo($generateAnnot val id: Int)
            """.trimIndent()
        }
    }

    @Test
    fun testMissingTransitiveRemapper() {
        compileWithFail("Property transitive of Bar appears remappable, but this class is not") {
            """
                $annotatedDecl
                data class Bar(val transitive : Foo)
            """.trimIndent()
        }
    }

    @Test
    fun testMissingRemapperInContainer() {
        compileWithFail("Property transitive of Bar appears remappable, but this class is not") {
            """
                $annotatedDecl
                data class Bar(val transitive : Map<Int, Foo>)
            """.trimIndent()
        }
    }

    @Test
    fun testUnsupportedRemapper() {
        compileWithFail("""Property contained of Woops cannot be auto-remapped""") {
            """
                $annotatedDecl

                $generateRemapper
                data class Woops(val contained: MutableSet<$testClass>)
            """.trimIndent()
        }
    }

    @Test
    fun testTypeAliases() {
        compileWithFail("""Property transitive of Bar appears remappable, but this class is not""") {
            """
                $annotatedDecl

                typealias A = $testClass?

                typealias B = List<A>?

                typealias C = Set<B?>?

                data class Bar(val transitive: List<C>)
            """.trimIndent()
        }
    }

    @Test
    fun testFloatingMetaKey() {
        compileWithFail(badGenerateAnnot) { """
            $generateAnnot
            val global = tac.MetaKey<Int>.named(0)
        """.trimIndent()
        }
    }

    @Test
    fun testMutableMetaKey() {
        compileWithFail(badGenerateAnnot) { """
            object Foo {
                $generateAnnot
                var META : $metaKey = $metaKey.named(0)
            }
        """.trimIndent()}
    }

    @Test
    fun testWrongTypeKey() {
        compileWithFail(badGenerateAnnot) { """
            object Foo {
                $generateAnnot
                val META : tac.MetaKey<String> = tac.MetaKey<String>(0)
            }
        """.trimIndent()
        }
    }

    @Test
    fun testNotObjectClass() {
        compileWithFail(badGenerateAnnot) { """
            class Foo {
               $generateAnnot
               val META : $metaKey = $metaKey.named(0)
            }
        """.trimIndent()
        }
    }

    @Test
    fun testCorrectMetaKeyAnnotation() {
        compileSuccess {
            """
                object Foo {
                   $generateAnnot
                   val META : $metaKey = $metaKey.named(0)
                }
            """.trimIndent()
        }
    }
}
