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
class MustHaveKSerializableTest(val env: KotlinCoreEnvironment) {

    val library1 = """
        package kotlinx.serialization
        annotation class Serializable
    """

    val library2 = """
        package utils
        interface HasKSerializable
    """

    fun failureCount(code: String) =
        MustHaveKSerializable(TestConfig()).lintWithContext(env, code, library1, library2).size

    @Test
    fun simpleClassFails() {
        val code = """
            class Foo : utils.HasKSerializable
        """
        assertEquals(1, failureCount(code))
    }

    @Test
    fun simpleClassWithSerializablePasses() {
        val code = """
            @kotlinx.serialization.Serializable
            class Foo : utils.HasKSerializable
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun objectFails() {
        val code = """
            object Foo : utils.HasKSerializable
        """
        assertEquals(1, failureCount(code))
    }


    @Test
    fun objectWithSerializablePasses() {
        val code = """
            @kotlinx.serialization.Serializable
            object Foo : utils.HasKSerializable
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun abstractClassFails() {
        val code = """
            abstract class Foo : utils.HasKSerializable
        """
        assertEquals(1, failureCount(code))
    }

    @Test
    fun sealedClassFails() {
        val code = """
            sealed class Foo : utils.HasKSerializable
        """
        assertEquals(1, failureCount(code))
    }

    @Test
    fun interfacePasses() {
        val code = """
            interface Foo : utils.HasKSerializable
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun derivedClassFails() {
        val code = """
            @kotlinx.serialization.Serializable
            class Foo : utils.HasKSerializable
            class Bar : Foo()
        """
        assertEquals(1, failureCount(code))
    }

    @Test
    fun derivedClassWithSerializablePasses() {
        val code = """
            @kotlinx.serialization.Serializable
            class Foo : utils.HasKSerializable
            @kotlinx.serialization.Serializable
            class Bar : Foo()
        """
        assertEquals(0, failureCount(code))
    }
}

