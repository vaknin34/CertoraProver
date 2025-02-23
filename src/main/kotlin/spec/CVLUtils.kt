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
package spec

import analysis.maybeNarrow
import bridge.ContractInstanceInSDC
import log.Logger
import log.LoggerTypes
import rules.RuleCheckResult
import scene.ICVLScene
import spec.cvlast.*
import spec.cvlast.typechecker.CVLError
import statistics.RunIDFactory
import tac.CallId
import tac.MetaKey
import tac.Tag
import utils.CollectingResult
import utils.filterToSet
import vc.data.*
import vc.data.TACMeta.CVL_DEF_SITE
import vc.data.TACMeta.CVL_VAR

private val logger = Logger(LoggerTypes.COMMON)

/**
 * Random utils that need to be sorted, especially focused on counterexample processing
 */
class CVLTestGenerator {
    var contractName: String? = null

    companion object {
        /**
         *
         * @param methodsFromContract method declarations that were imported from one of the checked contracts (as
         *  opposed to the `methods`-block inside the CVL file)
         */
        fun parseCheckCVL(
            cvlInput: CVLInput,
            contracts: List<ContractInstanceInSDC>,
            mainContract: ContractInstanceInSDC,
            scene: ICVLScene
        ): CollectingResult<CVL, CVLError> {
            return CVLAstBuilder(
                cvlInput,
                contracts,
                mainContract,
                scene,
                object : IRunIdFactory {
                    override fun reportCVL(cvlFile: String, ast: CVLAst) {
                        RunIDFactory.runId().reportCVL(cvlFile, ast)
                    }
                }
            ).build()
        }

        fun getAssertionMessage(violatedAssertions_: List<RuleCheckResult.RuleFailureMeta>, isSatisfy: Boolean): String {
            var violatedAssertionsMessages = violatedAssertions_.map { it.message }.toSet()
            if (violatedAssertionsMessages.isEmpty()) {
                logger.warn { "No violated assertion found" }
            } else {
                if (violatedAssertionsMessages.size > 1) {
                    val multiViolatedAssertions = if(isSatisfy) {
                        mutableSetOf("Multiple witnesses generated.")
                    } else {
                        mutableSetOf("Multiple assertions violated.")
                    }
                    multiViolatedAssertions.addAll(violatedAssertionsMessages)
                    violatedAssertionsMessages =  multiViolatedAssertions
                }
            }
            return violatedAssertionsMessages.joinToString(" ")
        }

        private fun getVarsWithMeta(tacObject: CoreTACProgram, key: MetaKey<*>): Set<TACSymbol.Var> =
            tacObject.analysisCache.graph.commands.mapNotNullTo(mutableSetOf()) { lcmd ->
                lcmd.maybeNarrow<TACCmd.Simple.AssigningCmd>()?.cmd?.lhs?.takeIf { s -> s.meta.containsKey(key) }
            } + tacObject.analysisCache.graph.commands.flatMap { lcmd ->
                lcmd.cmd.getFreeVarsOfRhs().mapNotNull { s -> s.takeIf { it.meta.containsKey(key) } }
            }

        fun getCVLVars(tacObject: CoreTACProgram): Set<TACSymbol.Var> = getVarsWithMeta(tacObject, CVL_VAR)

        fun getCVLLocalVars(tacObject: CoreTACProgram): Set<TACSymbol.Var> =
            getCVLVars(tacObject).filterToSet { it.meta[CVL_DEF_SITE] is CVLDefinitionSite.Rule }
    }

}

fun CVLKeywords.toVar(
    t: Tag = this.type.toTag(),
    callIndex: CallId = TACSymbol.Var.DEFAULT_INDEX
): TACSymbol.Var {
    return TACKeyword.values().singleOrNull {
        it.cvlCorrespondence == this
    }?.toVar() ?: getCVLVariable(this.name, callIndex, t, cvlDefSite = CVLDefinitionSite.Rule(range = null), true, this.type).let {
        it.withMeta { it + this.meta.add(TACSymbol.Var.KEYWORD_ENTRY to TACSymbol.Var.KeywordEntry(this.keyword)) }
    }
}


fun CVLReservedVariables.toVar(t: Tag = Tag.Bit256, idx: Int? = null) =
    TACSymbol.Var(this.name, t).let {
        if (idx == null) {
            it
        } else {
            it.withSuffix(idx)
        }
    }
