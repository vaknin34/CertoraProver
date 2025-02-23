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

package analysis.integeroverflows

import analysis.integeroverflows.OverflowTestAux.TestConfig
import analysis.integeroverflows.OverflowTestAux.checkAdd
import analysis.integeroverflows.OverflowTestAux.configSequence
import analysis.integeroverflows.OverflowTestAux.simpleBinarySpecAndContract
import annotations.TestTags
import infra.CertoraBuild.Companion.EVMCompiler
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test

@Tag(TestTags.EXPENSIVE)
class AdditionOverflowTest {

    private fun TestConfig.testAddition() =
        test(
            simpleBinarySpecAndContract("+"),
            { checkAdd(it, additionMeta) },
            toString()
        )

        @Test
        fun additionTest() {
            configSequence(8, 240, 256).forEach { it.testAddition() }
        }

        @Test
        fun justOneTest() {
            TestConfig(
                compiler = EVMCompiler.Vyper("vyper0.3.9"),
                signed = true,
                optimize = false,
                viaIR = false,
                withRevert = false,
                width = 8,
            ).testAddition()
        }
    }
