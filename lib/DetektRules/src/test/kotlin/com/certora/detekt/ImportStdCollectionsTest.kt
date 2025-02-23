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

package com.certora.detekt

import io.gitlab.arturbosch.detekt.rules.KotlinCoreEnvironmentTest
import io.gitlab.arturbosch.detekt.test.*
import org.jetbrains.kotlin.cli.jvm.compiler.KotlinCoreEnvironment
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions.*

@KotlinCoreEnvironmentTest
class ImportStdCollectionsTest(val env: KotlinCoreEnvironment) {

    val library = """
        package datastructures.stdcollections
        import kotlin.collections.setOf as kSetOf
        import kotlin.collections.plus as kPlus

        inline fun <T> setOf(): Set<T> = kSetOf()
        operator fun <T> Set<T>.plus(elements: Iterable<T>): Set<T> = this.kPlus(elements)
    """

    fun failureCount(code: String) =
        ImportStdCollections(TestConfig()).lintWithContext(env, code, library).size

    @Test
    fun simpleFunctionCallFails() {
        val code = """
            val foo get() = setOf<Int>()
        """
        assertEquals(1, failureCount(code))
    }

    @Test
    fun simpleFunctionCallWithImportPasses() {
        val code = """
            import datastructures.stdcollections.*
            val foo get() = setOf<Int>()
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun importAliasCallPasses() {
        val code = """
            import kotlin.collections.setOf as kSetOf
            val foo get() = kSetOf<Int>()
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun qualifiedCallPasses() {
        val code = """
            val foo get() = kotlin.collections.setOf<Int>()
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun operatorFails() {
        val code = """
            import kotlin.collections.setOf as kSetOf
            val foo get() = kSetOf<Int>() + kSetOf<Int>()
        """
        assertEquals(1, failureCount(code))
    }

    @Test
    fun operatorWithImportPasses() {
        val code = """
            import kotlin.collections.setOf as kSetOf
            import datastructures.stdcollections.*
            val foo get() = kSetOf<Int>() + kSetOf<Int>()
        """
        assertEquals(0, failureCount(code))
    }

}

