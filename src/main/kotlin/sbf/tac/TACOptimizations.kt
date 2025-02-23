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

package sbf.tac

import analysis.controlflow.InfeasiblePaths
import analysis.loop.LoopHoistingOptimization
import analysis.opt.*
import analysis.opt.inliner.GlobalInliner
import analysis.opt.intervals.IntervalsRewriter
import analysis.opt.overflow.OverflowPatternRewriter
import analysis.split.BoolOptimizer
import config.ReportTypes
import instrumentation.transformers.FilteringFunctions
import instrumentation.transformers.TACDSA
import instrumentation.transformers.optimizeAssignments
import optimizer.Pruner
import sbf.SolanaConfig
import utils.*
import vc.data.CoreTACProgram
import verifier.BlockMerger
import verifier.CoreToCoreTransformer
import verifier.SimpleMemoryOptimizer
import wasm.WasmEntryPoint

fun optimize(coreTAC: CoreTACProgram, isSatisfyRule: Boolean): CoreTACProgram {
    val preprocessed = CoreTACProgram.Linear(coreTAC)
        .map(CoreToCoreTransformer(ReportTypes.DSA, TACDSA::simplify))
        .map(CoreToCoreTransformer(ReportTypes.HOIST_LOOPS, LoopHoistingOptimization::hoistLoopComputations))
        .map(CoreToCoreTransformer(ReportTypes.UNROLL, CoreTACProgram::convertToLoopFreeCode))
        .mapIf(isSatisfyRule, CoreToCoreTransformer(ReportTypes.REWRITE_ASSERTS, WasmEntryPoint::rewriteAsserts))

    val maybeOptimized1 = runIf(SolanaConfig.EnableTACOptimizations.get() >= 1) {
        preprocessed
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.OPTIMIZE, ConstantPropagator::propagateConstants))
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.OPTIMIZE, ConstantComputationInliner::rewriteConstantCalculations))
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.OPTIMIZE_BOOL_VARIABLES) { c -> BoolOptimizer(c).go() })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.PROPAGATOR_SIMPLIFIER) { ConstantPropagatorAndSimplifier(it).rewrite() })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.NEGATION_NORMALIZER) { NegationNormalizer(it).rewrite() })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.PATTERN_REWRITER) { PatternRewriter.rewrite(it, PatternRewriter::earlyPatternsList) })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.GLOBAL_INLINER) { GlobalInliner.inlineAll(it) })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.UNUSED_ASSIGNMENTS) {
                optimizeAssignments(it, FilteringFunctions.default(it, keepRevertManagment = true))
                    .let(BlockMerger::mergeBlocks)
            })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.OPTIMIZE_OVERFLOW) { OverflowPatternRewriter(it).go() })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.COLLAPSE_EMPTY_DSA, TACDSA::collapseEmptyAssignmentBlocks))
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.OPTIMIZE_PROPAGATE_CONSTANTS1) {
                ConstantPropagator.propagateConstants(it, emptySet()).let {
                    BlockMerger.mergeBlocks(it)
                }
            })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.REMOVE_UNUSED_WRITES, SimpleMemoryOptimizer::removeUnusedWrites))
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.OPTIMIZE) { c ->
                optimizeAssignments(
                    c,
                    FilteringFunctions.default(c, keepRevertManagment = true)
                ).let(BlockMerger::mergeBlocks)
            })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.PATH_OPTIMIZE1) { Pruner(it).prune() })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.INTERVALS_OPTIMIZE) {
                IntervalsRewriter.rewrite(it, handleLeinoVars = false, preserve = { false })
            })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.PATH_OPTIMIZE1) { Pruner(it).prune() })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.OPTIMIZE_DIAMONDS) { simplifyDiamonds(it, iterative = true) })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.OPTIMIZE_PROPAGATE_CONSTANTS2) {
                // after pruning infeasible paths, there are more constants to propagate
                ConstantPropagator.propagateConstants(it, emptySet())
            })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.PATH_OPTIMIZE2) { Pruner(it).prune() })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.OPTIMIZE_MERGE_BLOCKS, BlockMerger::mergeBlocks))
    }

    val maybeOptimized2 = runIf(SolanaConfig.EnableTACOptimizations.get() >= 2) {
        check(maybeOptimized1 != null) { "Unexpected problem in Solana TAC optimizer -O2"}
        maybeOptimized1
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.GLOBAL_INLINER) { GlobalInliner.inlineAll(it) })
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.OPTIMIZE_PROPAGATE_CONSTANTS1) {
                ConstantPropagator.propagateConstants(it, emptySet()).let {
                    BlockMerger.mergeBlocks(it)
                }
            })
    }

    val maybeOptimized3 = runIf(SolanaConfig.EnableTACOptimizations.get() >= 3) {
        check(maybeOptimized2 != null) { "Unexpected problem in Solana TAC optimizer -O3"}
        maybeOptimized2
            .mapIfAllowed(CoreToCoreTransformer(ReportTypes.OPTIMIZE_INFEASIBLE_PATHS) {
                InfeasiblePaths.doInfeasibleBranchAnalysisAndPruning(
                    it
                )
            })
    }

    return maybeOptimized3?.ref ?: (maybeOptimized2?.ref ?: (maybeOptimized1?.ref ?: preprocessed.ref))
}

