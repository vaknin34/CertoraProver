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

package smtlibutils.cmdprocessor

import solver.SolverConfig
import solver.Z3SolverInfo
import kotlin.time.Duration

/**
 * Information about an instance of an external solver.
 * Should store everything we know about a such an instance, in particular how to recreate it.
 *
 * In contrast to [SolverConfig], this uses the data structures of SMTLibUtils, like [CmdProcessor.Options].
 *
 * Can be generated from [SolverConfig].
 * We use this class to spawn actual solvers in the SMTLibUtils infrastructure.
 */
sealed class SolverInstanceInfo {
    abstract val solverConfig: SolverConfig

    abstract val options: CmdProcessor.Options
    abstract val name: String

    abstract val critical: Boolean

    /** We cannot call this `copy` because of an overriding conflict with the data class [Standard]'s implicit copy
     * method. */
    fun copy1(
        solverConfig: SolverConfig = this.solverConfig,
        timelimit: Duration? = this.solverConfig.timelimit,
        options: CmdProcessor.Options = this.options,
        name: String = this.name,
    ): SolverInstanceInfo =
        when (this) {
            None -> this
            is Standard ->
                this.copy(
                    solverConfig = solverConfig.copy(timelimit = timelimit, incremental = options.incremental),
                    options = options,
                    name = name,
                )
        }

    val actualCommand: List<String>
        get() = solverConfig.getCommandline()

    data class Standard(
        override val solverConfig: SolverConfig,
        override val options: CmdProcessor.Options,
        override val name: String = solverConfig.fullName,
        override val critical: Boolean
    ) : SolverInstanceInfo()

    object None : SolverInstanceInfo() {
        override val solverConfig: SolverConfig
            get() = error("not available")
        override val options: CmdProcessor.Options
            get() = error("not available")
        override val name: String
            get() = error("not available")
        override val critical: Boolean
            get() = true // In case this gets used, don't set the OOM score adjustment

        override fun toString(): String {
            return "SolverIstanceInfo.NONE"
        }
    }

    companion object {
        /** [SolverInstanceInfo] corresponding to a basic z3 instance. */
        fun plainZ3(timeout: Duration, options: CmdProcessor.Options? = null) =
            fromSolverConfig(Z3SolverInfo.plainConfig(timeout), options ?:CmdProcessor.Options.Default, critical = true)


        fun fromSolverConfig(
            solverConfig: SolverConfig,
            options: CmdProcessor.Options,
            critical: Boolean = true,
            name: String = solverConfig.fullName,
        ): Standard {
            check(solverConfig.incremental == options.incremental)
            { "inconsistent 'incremental' settings between $solverConfig and $options" }
            return Standard(
                solverConfig,
                options,
                name,
                critical
            )
        }

        operator fun invoke(
            solverConfig: SolverConfig,
            options: CmdProcessor.Options,
            critical: Boolean = true,
            name: String = solverConfig.fullName,
        ) = Standard(solverConfig, options, name, critical)

        fun reduce(s1: SolverInstanceInfo, s2: SolverInstanceInfo): SolverInstanceInfo =
            when (s1) {
                None -> s2
                is Standard -> when (s2) {
                    None -> s1
                    is Standard -> error("cannot reduce two non-None SolverInstanceInfos: \"$s1\", \"$s2\"")
                }
            }
    }
}
