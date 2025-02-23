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

package analysis.externalcall

import annotation.ScopedMatrix
import annotation.SolidityConfigMatrix
import annotation.Z3Timeout
import annotations.TestTags.EXPENSIVE
import extension.ForceZ3Timeout
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.extension.ExtendWith
import org.junit.jupiter.params.ParameterizedTest

abstract class AbstractFreePointerSanityTest(partition: Int) : AbstractExternalCallCopyTest(partition) {

    private val allocBeforeAction = listOf({ s: String ->
        "uint init = $s.length;"
    }, { s: String ->
        "bytes memory x = abi.encodePacked($s);" +
                "uint init = x.length;"
    }, { s: String ->
        "uint[] memory y = new uint[](2);" +
                "y[0] = $s.length;" +
                "uint init = $s.length + y.length;"
    }, { s: String ->
        """
                    bytes memory x = abi.encodePacked($s);
                    uint[] memory y = new uint[](2);
                    y[0] = x.length;
                    uint init = y[0] + y[1] + x.length;
                """.trimIndent()
    }, { s: String ->
        """
                    uint[] memory y = new uint[](2);
                    bytes memory x = abi.encodePacked($s);
                    y[0] = x.length;
                    uint init = x.length + y[1];
                """.trimIndent()
    }, { s: String ->
        """
            bytes memory x = abi.encode($s);
            uint init = x.length;
        """.trimIndent()
    }, { s: String ->
        """
            bytes memory x = abi.encode($s);
            uint[] memory y = new uint[](2);
            y[0] = x.length;
            uint init = x.length + y.length;
        """.trimIndent()
    }, { s: String ->
        """
            uint[] memory y = new uint[](2);
            bytes memory x = abi.encode($s);
            y[0] = x.length;
            uint init = x.length + y.length;
        """.trimIndent()
    })

    @ParameterizedTest
    @ScopedMatrix
    fun testFreePointerSanity(solc: String, optimize: Boolean, pragma: String) {
        val beforeAlloc = allocBeforeAction
        for(input in inner) {
            for(output in outer) {
                for(bAlloc in beforeAlloc) {
                    val prefix = bAlloc("nondet")
                    val contract = """
                        $pragma

                        contract Test {
                             function extCall($input memory input) public returns ($output memory) {
                                return new $output(input.length);
                             }

                             function test($input memory nondet) public returns (uint) {
                                 $prefix
                                 $input memory d = new $input(init); // provided by bAlloc
                                 $output memory out = this.extCall(d);
                                 return out.length;
                             }
                        }
                    """.trimIndent()
                    this.runTestPipeline(contractSource = contract, optimize = optimize, solc = solc) {
                        "With $solc, $optimize, [$pragma], in = $input, out = $output,\n $prefix"
                    }
                }
            }
        }
    }
}

@SolidityConfigMatrix(
    withHeaders = true,
    withOptimizeFlag = true
)
@ExtendWith(ForceZ3Timeout::class)
@Z3Timeout(timeoutMs = 3000)
@Tag(EXPENSIVE)
class FreePointerSanityPartition0 : AbstractFreePointerSanityTest(0)

@SolidityConfigMatrix(
    withHeaders = true,
    withOptimizeFlag = true
)
@ExtendWith(ForceZ3Timeout::class)
@Z3Timeout(timeoutMs = 3000)
@Tag(EXPENSIVE)
class FreePointerSanityPartition1 : AbstractFreePointerSanityTest(1)

@SolidityConfigMatrix(
    withHeaders = true,
    withOptimizeFlag = true
)
@ExtendWith(ForceZ3Timeout::class)
@Z3Timeout(timeoutMs = 3000)
@Tag(EXPENSIVE)
class FreePointerSanityPartition2 : AbstractFreePointerSanityTest(2)

@SolidityConfigMatrix(
    withHeaders = true,
    withOptimizeFlag = true
)
@ExtendWith(ForceZ3Timeout::class)
@Z3Timeout(timeoutMs = 3000)
@Tag(EXPENSIVE)
class FreePointerSanityPartition3 : AbstractFreePointerSanityTest(3)

@SolidityConfigMatrix(
    withHeaders = true,
    withOptimizeFlag = true
)
@ExtendWith(ForceZ3Timeout::class)
@Z3Timeout(timeoutMs = 3000)
@Tag(EXPENSIVE)
class FreePointerSanityPartition4 : AbstractFreePointerSanityTest(4)

@SolidityConfigMatrix(
    withHeaders = true,
    withOptimizeFlag = true
)
@ExtendWith(ForceZ3Timeout::class)
@Z3Timeout(timeoutMs = 3000)
@Tag(EXPENSIVE)
class FreePointerSanityPartition5 : AbstractFreePointerSanityTest(5)

@SolidityConfigMatrix(
    withHeaders = true,
    withOptimizeFlag = true
)
@ExtendWith(ForceZ3Timeout::class)
@Z3Timeout(timeoutMs = 3000)
@Tag(EXPENSIVE)
class FreePointerSanityPartition6 : AbstractFreePointerSanityTest(6)

@SolidityConfigMatrix(
    withHeaders = true,
    withOptimizeFlag = true
)
@ExtendWith(ForceZ3Timeout::class)
@Z3Timeout(timeoutMs = 3000)
@Tag(EXPENSIVE)
class FreePointerSanityPartition7 : AbstractFreePointerSanityTest(7)

@SolidityConfigMatrix(
    withHeaders = true,
    withOptimizeFlag = true
)
@ExtendWith(ForceZ3Timeout::class)
@Z3Timeout(timeoutMs = 3000)
@Tag(EXPENSIVE)
class FreePointerSanityPartition8 : AbstractFreePointerSanityTest(8)
