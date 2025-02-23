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

package smt

import cli.ConstraintChooserConverter
import ksp.dynamicconversion.AddDynamicConversion
import ksp.dynamicconversion.ConvertibleWith
import ksp.dynamicconversion.DynamicConverter
import solver.Configuration
import solver.Configurable
import solver.SolverConfig
import java.io.Serializable
import kotlin.time.Duration
import java.util.concurrent.atomic.AtomicInteger

/**
 * Configuration for CEGAR-based solving. Mostly consists of a bunch of worker configurations.
 */
@AddDynamicConversion
data class CEGARConfig(
    val name: String,
    val timelimit: Duration,
    @ConvertibleWith(WorkerConfig.Converter::class)
    val workers: List<WorkerConfig> = WorkerConfig.values,
    @ConvertibleWith(SolverConfig.Converter::class)
    val niaWorkers: List<SolverConfig> = listOf(
        SolverConfig.z3.def.copy(incremental = false),
        SolverConfig.cvc5.def.copy(incremental = false),
        SolverConfig.cvc4.nonlin.copy(incremental = false),
    ).filter { it.solverInfo.isAvailable() },
    override val configList: List<Configurable>? = null,
) : Configurable, Serializable {

    class Converter: DynamicConverter<CEGARConfig> {
        override fun invoke(v: Any) = CEGARConfig.construct(v, CEGARConfig)
    }

    /**
     * Configuration class for a single CEGAR worker.
     */
    @AddDynamicConversion
    data class WorkerConfig(
        val name: String,
        @ConvertibleWith(SolverConfig.Converter::class)
        val liaConfig: SolverConfig,
        @ConvertibleWith(SolverConfig.Converter::class)
        val niaConfig: SolverConfig,
        val learn: Boolean = false,
        @ConvertibleWith(ConvertConstraintChooser::class)
        val constraintChooser: ConstraintChooserEnum = ConstraintChooserEnum.justBools,
        val modelDiff: Boolean = true,
        val modelDiffThreshold: Int = 5,
        val niaRelaxations: Int = 3,
        override val configList: List<Configurable>? = null,
    ): Configurable, Serializable {

        class Converter: DynamicConverter<WorkerConfig> {
            override fun invoke(v: Any) = WorkerConfig.construct(v, WorkerConfig)
        }
        class ConvertConstraintChooser: DynamicConverter<ConstraintChooserEnum> {
            override fun invoke(v: Any) = ConstraintChooserConverter.convert(v.toString())
        }

        val workerID: Int = nextWorkerID.getAndIncrement()

        override val configName: String = name
        override fun asConfigList(expands: List<Configurable>) = this.copy(configList = expands)

        companion object: Configuration.Registry<WorkerConfig>("cegarWorker", "z3"),
            Configurable.ConversionHelper<WorkerConfig> {
            private val nextWorkerID: AtomicInteger = AtomicInteger(1)

            val z3 = register(
                WorkerConfig("z3",
                SolverConfig.z3.def.copy(incremental = true),
                SolverConfig.z3.def.copy(incremental = true),
            )
            )
            val cvc5 = register(
                WorkerConfig("cvc5",
                SolverConfig.cvc5.def.copy(
                    incremental = true,
                    clOptions = listOf("--output=learned-lits"),
                ),
                SolverConfig.cvc5.nonlin.copy(incremental = true),
                learn = true,
            )
            )
            val z3eq2 = register(
                WorkerConfig("z3eq2",
                SolverConfig.z3.eq2.copy(incremental = true),
                SolverConfig.z3.eq2.copy(incremental = true),
            )
            )
            val z3lia2 = register(
                WorkerConfig("z3lia2",
                SolverConfig.z3.lia2.copy(incremental = true),
                SolverConfig.z3.lia2.copy(incremental = true),
            )
            )

            override fun doCopy(t: WorkerConfig, override: Map<String, Any>?) = t.copy(override)
            override fun doConstruct(params: Map<String, Any>) = constructFrom(params)
        }

        fun finalizeConfig(timelimit: Duration, memlimit: Long?) = copy(
            liaConfig = liaConfig.copy(timelimit = timelimit, memlimitBytes = memlimit),
            niaConfig = liaConfig.copy(timelimit = timelimit, memlimitBytes = memlimit),
        )
    }

    companion object: Configuration.Registry<CEGARConfig>("cegar", "def"), Configurable.ConversionHelper<CEGARConfig> {

        val def = register(
            CEGARConfig(
                "def",
                timelimit = Duration.ZERO,
                workers = listOf(
                    WorkerConfig.z3,
                    WorkerConfig.cvc5,
                    WorkerConfig.z3eq2,
                    WorkerConfig.z3lia2,
                ).filter { it.liaConfig.solverInfo.isAvailable() && it.niaConfig.solverInfo.isAvailable() },
                niaWorkers = listOf(
                    SolverConfig.z3.def.copy(incremental = false),
                    SolverConfig.cvc5.def.copy(incremental = false),
                    SolverConfig.cvc4.nonlin.copy(incremental = false),
                ).filter { it.solverInfo.isAvailable() },
            )
        )

        override fun doCopy(t: CEGARConfig, override: Map<String, Any>?) = t.copy(override)
        override fun doConstruct(params: Map<String, Any>) = constructFrom(params)
    }

    override val configName = name
    override fun asConfigList(expands: List<Configurable>) = this.copy(configList = expands)
}
