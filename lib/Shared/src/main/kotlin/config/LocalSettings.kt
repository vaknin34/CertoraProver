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

package config

import smt.BackendStrategyEnum
import smt.UseLIAEnum
import solver.SolverChoice
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

/**
 * [LocalSettings] makes possible to run multiple rules and methods with different configuration for each of them.
 * Particularly, it is used in [TACVerifier], [LExpVcChecker], and classes related to the parallel splitter,
 * where the global [Config] object was used previously to configure behaviour of Prover.
 * So far, the main application of [LocalSettings] is in [TimeoutCracker] where it enables running the portfolio
 * of configurations for the different rule/method pairs in parallel. Therefore [LocalSettings] contains now only
 * options used in the configurations from the portfolio of TimeoutCracker.
 * Note that if you want to add an option to [LocalSettings] which is so far read from [Config] you need to:
 * 1) replace all places where is a value of the option read from [Config] by reading from [LocalSettings],
 * 2) propagate it in [LExpVcCheckerConfig.fromLocalSettings] if it used in [LExpVcChecker],
 */
data class LocalSettings(
    val depth: Int = Config.Smt.SplittingDepth,
    val dontStopAtFirstSplitTimeout: Boolean = Config.DontStopAtFirstSplitTimeout.get(),
    val parallelSplittingTimelimit: Duration = Config.ParallelSplittingTimelimit.get().seconds,
    val parallelSplitting: Boolean = Config.ParallelSplitting.get(),
    val parallelSplitterLIASolvers: SolverChoice = SolverChoice(Config.ParallelSplitterLIASolvers.get().toList()),
    val parallelSplitterNIASolvers: SolverChoice = SolverChoice(Config.ParallelSplitterNIASolvers.get().toList()),
    val solverTimeout: Duration = Config.SolverTimeout.get().seconds,
    val userGlobalTimeout: Duration = Config.UserGlobalTimeout.get().seconds,
    val globalTimeout: Duration = Config.GlobalTimeout.get().seconds,
    val initialSplitDepth: Int = Config.Smt.InitialSplitDepth.get(),
    val solverProgramChoice: SolverChoice = SolverChoice(Config.SolverProgramChoice.get().toList()),
    val nonLinearArithmetic: Boolean = Config.Smt.UseNIA.get(),
    val useLIA: UseLIAEnum = Config.Smt.UseLIA.get(),
    val overrideSolvers: Boolean = Config.Smt.OverrideSolvers.get(),
    val parallelSplittingInitialDepth: Int = Config.ParallelSplittingInitialDepth.get(),
    val backendStrategy: BackendStrategyEnum = Config.Smt.BackendStrategy.get()
) {
    val solverProgramChoiceDefault: Boolean = (solverProgramChoice == SolverChoice(Config.SolverProgramChoice.get().toList())
            && Config.SolverProgramChoice.isDefault())
}
