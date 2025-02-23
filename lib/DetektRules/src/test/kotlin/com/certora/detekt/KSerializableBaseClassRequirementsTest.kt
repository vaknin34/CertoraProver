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
class KSerializableBaseClassRequirementsTest(val env: KotlinCoreEnvironment) {

    val library1 = """
        package kotlinx.serialization
        annotation class Serializable
    """

    val library2 = """
        package utils
        interface HasKSerializable
    """

    fun failureCount(code: String) =
    KSerializableBaseClassRequirements(TestConfig()).lintWithContext(env, code, library1, library2).size

    @Test
    fun plainOpenClassPasses() {
        val code = """
            open class Foo
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun openClassWithInterfaceWithoutAnnotationPasses() {
        val code = """
            open class Foo : utils.HasKSerializable
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun openClassWithoutInterfaceWithAnnotationFails() {
        val code = """
            @kotlinx.serialization.Serializable
            open class Foo
        """
        assertEquals(1, failureCount(code))
    }

    @Test
    fun sealedClassWithInterfaceWithAnnotationPasses() {
        val code = """
            @kotlinx.serialization.Serializable
            sealed class Foo : utils.HasKSerializable
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun implicitlyFinalClassWithInterfacePasses() {
        val code = """
            class Foo : utils.HasKSerializable
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun finalClassWithInterfacePasses() {
        val code = """
            final class Foo : utils.HasKSerializable
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun implicitlyFinalClassWithSerializablePasses() {
        val code = """
            @kotlinx.serialization.Serializable
            class Foo
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun finalClassWithSerializablePasses() {
        val code = """
            @kotlinx.serialization.Serializable
            final class Foo
        """
        assertEquals(0, failureCount(code))
    }
}

