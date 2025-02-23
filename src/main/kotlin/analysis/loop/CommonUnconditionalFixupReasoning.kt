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

package analysis.loop

import analysis.TACBlock
import analysis.TACCommandGraph
import analysis.smtblaster.IBlaster
import analysis.smtblaster.SmtExpIntTermBuilder
import parallel.Parallel
import parallel.maybeMap
import vc.data.TACExpr
import vc.data.TACSymbol

/** Logic for checking if the successor of a copy loop is a fixup block */
abstract class CommonUnconditionalFixupReasoning(blaster: IBlaster, graph: TACCommandGraph) : CommonFixupReasoning(zBlaster = blaster, builder = SmtExpIntTermBuilder, me = graph.cache.gvn) {

    override fun findPostWriteFixup(g: TACCommandGraph, smtCommandGen: Generator, soleSuccBlock: TACBlock, loopConds: LoopConditions, loopInstantiations: LoopInstantiations): Parallel<PostWriteFixup?> {
        val state = mutableMapOf<TACSymbol.Var, TACExpr>()
        val mapper = makeStateMapper(state, loopInstantiations)

        return checkFixupBlock(smtCommandGen, soleSuccBlock, state, mapper).maybeMap {
            PostWriteFixup.SplitFixup(it.fixupEnd, inputAccess = it.inputAccess, outputAccess = it.outputAccess)
        }
    }
}
