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

package analysis.icfg

import com.certora.collect.*
import datastructures.MultiMap
import datastructures.add
import datastructures.mutableMultiMapOf
import datastructures.stdcollections.*
import instrumentation.transformers.CodeTransformer
import log.*
import tac.Tag
import utils.*
import vc.data.*
import vc.data.tacexprutil.getFreeVars
import utils.filterToSet
import java.io.Serializable

/**
 * A sourced axiom is a pair of a [TACAxiom] and the name of the ghost holding the axiom.
*/
private typealias SourcedAxiom = Pair<TACAxiom, String>
private typealias AxiomGrouping = MultiMap<TACSymbol.Var, SourcedAxiom>

private val logger = Logger(LoggerTypes.SPEC)

/**
 * We are inlining axioms in an early stage, so analyses and optimizations will be axiom aware.
 * This is assumed to be done before DSA, such that the variable names are always the same, and finding
 * the location to inline axioms is easy.
 *
 * The algorithm is as such: Inline between two writes if there exists a read. Root is considered a write.
 * There is a fine point to notice, that axioms could be dependent on each other.
 * Because axioms are assumed, order doesn't matter, so writing between two writes can reduce the amount of generated
 * forall expressions.
 */
object AxiomInliner : CodeTransformer()  {

    private fun groupAxioms(axioms: UfAxioms): AxiomGrouping {
        val res = mutableMultiMapOf<TACSymbol.Var, SourcedAxiom>()
        axioms.mapTo { axiomMap ->
            // Axiom map is actually from a ghost to list of axioms, but there is not real limitation that the axiom
            // needs to hold for said ghost only, so we ignore the key
            for ((ghost, axiomList) in axiomMap.entries) {
                for (a in axiomList) {
                    val vars = a.exp.getFreeVars()
                    for (v in vars) {
                        res.add(v, a to ghost.name)
                    }
                }
            }
        }
        return res
    }

    @Treapable
    sealed interface AxiomInlineReason: AmbiSerializable {
        @KSerializable
        object Root: AxiomInlineReason, Serializable {
            private fun readResolve(): Any = Root
            override fun hashCode() = hashObject(this)
        }

        @KSerializable
        data class Write(val variable: TACSymbol.Var): AxiomInlineReason, Serializable
    }
    @Treapable
    @KSerializable
    data class PlacementInfo(val ghostName: String, val inlineReason: AxiomInlineReason)
        : AmbiSerializable

    override fun transform(ast: CoreTACProgram): CoreTACProgram {
        val axioms = groupAxioms(ast.ufAxioms)
        val graph = ast.analysisCache.graph

        val tmp = TACKeyword.TMP(Tag.Bool, suffix = "_assume_axiom")
        val allAxiomCmds = ast.ufAxioms.mapTo { it.entries.flatMap {  (ghost, axioms) -> axioms.flatMap { axiom ->
            createInlineCommands(ghost.name, null, axiom, tmp)
        }}}
        return ast.toPatchingProgram().apply {
            val todo = graph.commands.asIterable().filterToSet { it.cmd.getModifiedVar() != null }
            val roots = graph.roots
            for (ltac in todo + roots) {
                // Prepend only to root
                val prepend = allAxiomCmds.takeIf { ltac in roots }?.also {
                    logger.debug { "Inlining axioms @ Root(${ltac.ptr}). Axioms are from all ghosts."}
                }.orEmpty()
                // Append if lhs in axioms
                val lhs = graph.elab(ltac.ptr).cmd.getModifiedVar()?.takeIf { it in axioms }
                val append = lhs?.let {
                    logger.debug {  "Inlining axioms after write to $it @ ${ltac.ptr}. Axiom are from " +
                        axioms[it]!!.joinToString(",") { (_, ghostName) -> ghostName}
                    }
                    axioms[it]!!.flatMap { (axiom, ghostName) ->
                        createInlineCommands(ghostName, lhs, axiom, tmp)
                    }
                }.orEmpty()
                replaceCommand(ltac.ptr, prepend + listOf(ltac.cmd) + append)
            }
            addVarDecl(tmp)
            replaceUfAxioms(UfAxioms.empty())
        }.toCode(ast)
    }

    private fun createInlineCommands(
        ghostName: String,
        lhs: TACSymbol.Var?,
        axiom: TACAxiom,
        assumeVar: TACSymbol.Var
    ): List<TACCmd.Simple> {
        val placementInfo = PlacementInfo(
            ghostName,
            lhs?.let { AxiomInlineReason.Write(it) } ?: AxiomInlineReason.Root
        )
        return listOf(
            TACCmd.Simple.AnnotationCmd(TACMeta.AXIOM_INLINED, placementInfo),
            TACCmd.Simple.AssigningCmd.AssignExpCmd(assumeVar, axiom.exp),
            TACCmd.Simple.AssumeCmd(assumeVar)
        )
    }

}
