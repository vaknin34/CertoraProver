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
import com.tschuchort.compiletesting.kspWithCompilation
import com.tschuchort.compiletesting.symbolProcessorProviders
import ksp.classlists.ListClassesProvider
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class ListClassesTest {
    private val examples = SourceFile.kotlin("ListExample.kt",
        """
        package listexample
        import ksp.classlists.ListClasses

        enum class ExampleEnum { FOO, BAR, BAZ }

        @ListClasses
        annotation class DummyAnnotation(val x : String, val y : Int, val z : ExampleEnum, val w : Array<String>) {
            companion object
        }

        @ListClasses @Repeatable
        annotation class RepeatableDummyAnnotation(val x : String) {
            companion object
        }

        @DummyAnnotation(""${'"'}
            foo line 1
            foo line 2
            foo line 3
            ""${'"'}, 3, ExampleEnum.FOO, []
        )
        @RepeatableDummyAnnotation("foo repeat 1")
        @RepeatableDummyAnnotation("foo repeat 2")
        class Foo

        @DummyAnnotation("bar", 4, ExampleEnum.BAR, ["a","b","\"c\""])
        class Bar

        @DummyAnnotation("\"baz\"", 0, ExampleEnum.BAZ, [])
        @RepeatableDummyAnnotation("baz repeat 1")
        class Baz


        class Results {
            val instances = DummyAnnotation.instances
            val repeatables = RepeatableDummyAnnotation.instances
        }

        val x = DummyAnnotation.instances
        """.trimIndent()
    )

    /**
     * Compiles [examples], and checks that elements of `Results.instances` for `Foo`, `Bar`, and `Baz` match with the
     * annotations returned from reflection.
     */
    @Suppress("unchecked")
    @Test fun testInstances() {
        // compile the example
        val result = KotlinCompilation().apply {
            sources = listOf(examples)
            symbolProcessorProviders = listOf(ListClassesProvider())
            inheritClassPath = true
            kspWithCompilation = true
        }.compile()

        // extract the generated map
        val resultsClass = result.classLoader.loadClass("listexample.Results")
        val resultsObj   = resultsClass.getConstructor().newInstance()
        val resultsMap   = resultsClass.getMethod("getInstances").invoke(resultsObj) as Map<*,*>
        val repeatsMap   = resultsClass.getMethod("getRepeatables").invoke(resultsObj) as Map<*,*>

        // test the fields
        for(classname in listOf("listexample.Foo", "listexample.Bar", "listexample.Baz")) {
            val testClass = result.classLoader.loadClass(classname)
            val testAnnot = testClass.kotlin.annotations.first()

            for (field in listOf("x", "y", "z", "w")) {
                val fieldValueFromAnnot = getField(testAnnot, field)
                val fieldValueFromMap   = getField(resultsMap[testClass.kotlin], field)

                println("checking: $classname.DummyAnnotation.$field:")
                println("  by reflection: <$fieldValueFromAnnot>")
                println("  generated: <$fieldValueFromMap>")

                assertEquals(fieldValueFromAnnot, fieldValueFromMap)
            }

            // each class has one DummyAnnotation and k RepeatableDummyAnnotations
            println("checking sizes of repeatable annotation lists:")
            assertEquals(testClass.kotlin.annotations.size - 1, (repeatsMap[testClass.kotlin] as? List<*>)?.size ?: 0)
        }

        // test the repeatables
    }

    /** @return the value of [obj].[field] */
    private fun getField(obj : Any?, field : String) : Any? {
        val result = obj!!.javaClass.getMethod(field).invoke(obj)
        return when (result) {
            is Array<*> -> /* Array.equals is identity comparison */ result.toList()
            else -> result
        }
    }
}
