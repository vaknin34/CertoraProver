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
class SerializableObjectNeedsReadResolveTest(val env: KotlinCoreEnvironment) {
    val library = """
        package java.io
        interface Serializable
    """

    fun failureCount(code: String) =
        SerializableObjectNeedsReadResolve(TestConfig()).lintWithContext(env, code, library).size

    @Test
    fun nonSerializableObjectPasses() {
        val code = """
            object Foo
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun serializableObjectWithoutReadResolveFails() {
        val code = """
            object Foo : java.io.Serializable
        """
        assertEquals(1, failureCount(code))
    }

    @Test
    fun serializableObjectWithReadResolvePasses() {
        val code = """
            object Foo : java.io.Serializable {
                private fun readResolve(): Any = Foo
            }
        """
        assertEquals(0, failureCount(code))
    }

    @Test
    fun serializableObjectWithBadReadResolveSignatureFails() {
        val code = """
            object Foo : java.io.Serializable {
                private fun readResolve() = Foo
            }
        """
        assertEquals(1, failureCount(code))
    }

    @Test
    fun serializableObjectWithWrongReadResolveResultFails() {
        val code = """
            object Foo : java.io.Serializable {
                private fun readResolve(): Any = Bar
            }
            object Bar
        """
        assertEquals(1, failureCount(code))
    }
}
