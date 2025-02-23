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

import analysis.PointerAnalysis
import analysis.pta.INIT_FAILURE
import analysis.pta.TrivialPointsToInformation
import loaders.SingleMethodTest
import loaders.runPTA
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.function.ThrowingSupplier
import vc.data.CoreTACProgram
import vc.data.TACCmd
import java.util.function.Supplier

abstract class AbstractExternalCallCopyTest(private val partition: Int) : SingleMethodTest {
    private val types: List<String> = listOf(
        "address[]",
        "uint[]",
        "bytes"
    )

    init {
        check(partition >= 0 && partition < (types.size * types.size))
    }

    protected val inner : List<String> = listOf(types[partition / types.size])

    protected val outer : List<String> = listOf(types[partition % types.size])

    protected fun runTestPipeline(contractSource: String, solc: String, optimize: Boolean, f: (() -> String)? = null) {
        val graph = Assertions.assertDoesNotThrow(
            ThrowingSupplier {
            this.loadTestMethod(contractSource, solc, optimize)
        }, if(f != null) {
            Supplier { f() }
        } else {
            null
        })
        Assertions.assertFalse((graph.code as CoreTACProgram).ltacStream().anyMatch {
            it.cmd is TACCmd.Simple.AnnotationCmd && (it.cmd as TACCmd.Simple.AnnotationCmd).annot.k == INIT_FAILURE
        }, f)
        val pta = runPTA(graph)
        Assertions.assertTrue(pta !is TrivialPointsToInformation, f)
    }

}
