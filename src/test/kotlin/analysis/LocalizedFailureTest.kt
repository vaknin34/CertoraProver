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

import analysis.pta.FlowPointsToInformation
import analysis.pta.INIT_FAILURE
import analysis.pta.POP_ALLOCATION
import annotation.SolidityVersion
import annotation.SolidityVersions
import loaders.SolidityContractTest
import loaders.runPTA
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import scene.MethodAttribute
import vc.data.CoreTACProgram
import vc.data.TACCmd

class LocalizedFailureTest : SolidityContractTest {
    @ParameterizedTest
    @SolidityVersions([SolidityVersion.ANY_4])
    fun testInlineAssembly(solc: String) {
        val m = this.loadTestContractMethod("analysis/InlineAssembly.sol", solc, optimize = false)
        val g = (m.code as CoreTACProgram).analysisCache.graph
        Assertions.assertTrue(g.commands.map(LTACCmd::cmd).any {
            it is TACCmd.Simple.AnnotationCmd && it.annot.k == POP_ALLOCATION
        })
        // check that inline assembly is RIDDLED with errors
        val fallback = m.getContainingContract().getMethodByUniqueAttribute(MethodAttribute.Unique.Fallback)
        Assertions.assertNotNull(fallback)
        check(fallback != null)
        Assertions.assertTrue((fallback.code as CoreTACProgram).analysisCache.graph.commands.map(LTACCmd::cmd).any {
            it is TACCmd.Simple.AnnotationCmd && it.annot.k == INIT_FAILURE
        })

        // now check that the points to analysis happily completes on the test method
        val pts = runPTA(m)
        Assertions.assertTrue(pts is FlowPointsToInformation)
    }
}
