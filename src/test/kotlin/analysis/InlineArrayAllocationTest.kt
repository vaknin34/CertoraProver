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

package analysis

import analysis.pta.INIT_FAILURE
import analysis.pta.TrivialPointsToInformation
import annotations.TestTags
import loaders.SingleMethodTest
import loaders.runPTA
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test
import vc.data.CoreTACProgram

/**
 * A very simple class that just ensures someone doesn't delete [analysis.alloc.InlineArrayAllocationRewriter] again
 * thinking no tests depend on it...
 */
@Tag(TestTags.EXPENSIVE)
class InlineArrayAllocationTest : SingleMethodTest {
    /**
       This scenario is more thoroughly exercised in [analysis.externalcall.AbstractFreePointerSanityTest]
     */
    @Test
    fun simpleInlineArrayAllocTest() {
        val m = this.loadTestMethod("""
            contract Test {
            	function extCall(address[] memory input) public returns (bytes memory) {
            		return new bytes(input.length);
            	}

            	function test(bytes memory nondet) public returns (uint) {
            		uint init = nondet.length;
            		address[] memory d = new address[](init); // provided by bAlloc
            		bytes memory out = this.extCall(d);
            		return out.length;
            	}
            }
        """.trimIndent(), solc = "solc6.10", optimize = true)
        Assertions.assertFalse((m.code as CoreTACProgram).parallelLtacStream().anyMatch {
            it.maybeAnnotation(INIT_FAILURE) != null
        })
        Assertions.assertTrue(runPTA(m) !is TrivialPointsToInformation)
    }
}
