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

package analysis.opt.intervals

import org.junit.jupiter.api.Test
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder

class SpecialDefAnalysisTest : TACBuilderAuxiliaries() {

    @Test
    fun testMask() {
        val prog = TACProgramBuilder {
            b assign a
            nop
            label("here")
            b assign a
            nop
            b assign a
        }
        val sites = SiteAnalysis(prog.code.analysisCache.graph)

        println(sites.forwardUseSitesOf(prog.ptr("here"), a))
        println(sites.backwardsSitesOf(prog.ptr("here"), a))
    }


    @Test
    fun test2() {
        val prog = TACProgramBuilder {
            assert(x)
            nop
            a assign 4
            label("here")
            nop
            jump(1) {
                nop
                b assign a
            }
            jump(2) {
                c assign a
                assert(x)
                nop
            }
        }
        val def = SiteAnalysis(prog.code.analysisCache.graph)

        println(def.forwardUseSitesOf(prog.ptr("here"), a))

    }

}
