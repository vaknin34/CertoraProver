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

package verifier

import smt.HashingScheme
import smt.axiomgenerators.fullinstantiation.expnormalizer.ExpNormalizer
import smt.solverscript.LExpressionFactory
import smt.solverscript.SmtTheory
import smt.solverscript.SmtTheoryFeature
import vc.data.LExpression

/** Should contain everything that is needed to configure the SMT backend, i.e., everything that happens after
 * generation of the VC as LExpressions. This includes axiom generation, smt solver interaction, etc. */
class LExpToSmtSetupInfo(
    val targetTheory: SmtTheory,
    val hashingScheme: HashingScheme,
    val createAxiomGeneratorContainer: CreateAxiomGeneratorContainer,
    val createExpNormalizer: (LExpressionFactory) -> ExpNormalizer
) {
    override fun toString(): String = targetTheory.toString()

    companion object {
        /** Note: while the `-smt_arrayTheory` flag remains removed
         * we always call this with [useArrayTheory] set to `false`. We're not removing the parameter for the time being
         * though, as we might fix array theory and put it back to use. */
        fun UFLIAorAUFLIA(
            useArrayTheory: Boolean,
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config
        ) =
            if (useArrayTheory) {
                AUFLIA(useQuantifiers, createAxiomGeneratorContainerConfig)
            } else {
                UFLIA(useQuantifiers, createAxiomGeneratorContainerConfig)
            }

        /** Note: [useArrayTheory] is always `false`, see [UFLIAorAUFLIA] for more details. */
        fun UFLIAorAUFLIAPartial(
            useArrayTheory: Boolean,
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config,
            linearizationSelector: (LExpression) -> Boolean
        ) =
            if (useArrayTheory) {
                AUFPartialLIA(useQuantifiers, createAxiomGeneratorContainerConfig, linearizationSelector)
            } else {
                UFPartialLIA(useQuantifiers, createAxiomGeneratorContainerConfig, linearizationSelector)
            }


        /** Note: [useArrayTheory] is always `false`, see [UFLIAorAUFLIA] for more details. */
        fun UFNIAorAUFNIA(
            useArrayTheory: Boolean,
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config
        ) =
            if (useArrayTheory) {
                AUFNIA(useQuantifiers, createAxiomGeneratorContainerConfig)
            } else {
                UFNIA(useQuantifiers, createAxiomGeneratorContainerConfig)
            }

        /** Note: [useArrayTheory] is always `false`, see [UFLIAorAUFLIA] for more details. */
        fun UFBVorAUFBV(
            useArrayTheory: Boolean,
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config
        ) =
            if (useArrayTheory) {
                AUFBV(useQuantifiers, createAxiomGeneratorContainerConfig)
            } else {
                UFBV(useQuantifiers, createAxiomGeneratorContainerConfig)
            }

        fun AUFBV(
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config
        ): LExpToSmtSetupInfo {
            val theory = when (createAxiomGeneratorContainerConfig.hashingScheme) {
                is HashingScheme.Legacy,
                HashingScheme.PlainInjectivity ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "AUFBV")
                HashingScheme.Datatypes ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "AUFDTBV")
            }
            return LExpToSmtSetupInfo(
                theory,
                createAxiomGeneratorContainerConfig.hashingScheme,
                CreateAxiomGeneratorContainer.HashAxioms(createAxiomGeneratorContainerConfig),
                ExpNormalizer.create(
                    theory,
                    createAxiomGeneratorContainerConfig.hashingScheme,
                    createAxiomGeneratorContainerConfig.overflowChecks
                )
            )
        }

        fun AUFNIA(
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config
        ): LExpToSmtSetupInfo {
            val theory = when (createAxiomGeneratorContainerConfig.hashingScheme) {
                is HashingScheme.Legacy,
                HashingScheme.PlainInjectivity ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "AUFNIA")
                HashingScheme.Datatypes ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "AUFDTNIA")
            }
            return LExpToSmtSetupInfo(
                theory,
                createAxiomGeneratorContainerConfig.hashingScheme,
                CreateAxiomGeneratorContainer.BwHashInstantiation(createAxiomGeneratorContainerConfig),
                ExpNormalizer.create(
                    theory,
                    createAxiomGeneratorContainerConfig.hashingScheme,
                    createAxiomGeneratorContainerConfig.overflowChecks,
                    { false }
                )
            )
        }

        fun AUFPartialLIA(
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config,
            linearizationSelector: (LExpression) -> Boolean
        ): LExpToSmtSetupInfo {
            val theory = when (createAxiomGeneratorContainerConfig.hashingScheme) {
                is HashingScheme.Legacy,
                HashingScheme.PlainInjectivity ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "AUFNIA")
                HashingScheme.Datatypes ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "AUFDTNIA")
            }
            return LExpToSmtSetupInfo(
                theory,
                createAxiomGeneratorContainerConfig.hashingScheme,
                CreateAxiomGeneratorContainer.FullInstantiation(createAxiomGeneratorContainerConfig, linearizationSelector),
                ExpNormalizer.create(
                    theory,
                    createAxiomGeneratorContainerConfig.hashingScheme,
                    createAxiomGeneratorContainerConfig.overflowChecks,
                    linearizationSelector
                )
            )
        }

        fun AUFLIA(
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config
        ): LExpToSmtSetupInfo {
            val theory = when (createAxiomGeneratorContainerConfig.hashingScheme) {
                is HashingScheme.Legacy,
                HashingScheme.PlainInjectivity ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "AUFLIA")
                HashingScheme.Datatypes ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "AUFDTLIA")
            }
            return LExpToSmtSetupInfo(
                theory,
                createAxiomGeneratorContainerConfig.hashingScheme,
                CreateAxiomGeneratorContainer.FullInstantiation(createAxiomGeneratorContainerConfig),
                ExpNormalizer.create(
                    theory,
                    createAxiomGeneratorContainerConfig.hashingScheme,
                    createAxiomGeneratorContainerConfig.overflowChecks,
                    { true }
                )
            )
        }

        fun UFBV(
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config
        ): LExpToSmtSetupInfo {
            val theory = when (createAxiomGeneratorContainerConfig.hashingScheme) {
                is HashingScheme.Legacy,
                HashingScheme.PlainInjectivity ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "UFBV")
                HashingScheme.Datatypes ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "UFDTBV")
            }
            return LExpToSmtSetupInfo(
                theory,
                createAxiomGeneratorContainerConfig.hashingScheme,
                CreateAxiomGeneratorContainer.HashArrayAxioms(createAxiomGeneratorContainerConfig),
                ExpNormalizer.create(
                    theory,
                    createAxiomGeneratorContainerConfig.hashingScheme,
                    createAxiomGeneratorContainerConfig.overflowChecks
                )
            )
        }

        @Suppress("unused")
        fun ABV(
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config
        ): LExpToSmtSetupInfo {
            val theory = when (createAxiomGeneratorContainerConfig.hashingScheme) {
                is HashingScheme.Legacy,
                HashingScheme.PlainInjectivity ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "ABV")
                HashingScheme.Datatypes ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "ADTBV")
            }
            return LExpToSmtSetupInfo(
                theory,
                createAxiomGeneratorContainerConfig.hashingScheme,
                CreateAxiomGeneratorContainer.HashAxioms(createAxiomGeneratorContainerConfig),
                ExpNormalizer.create(
                    theory,
                    createAxiomGeneratorContainerConfig.hashingScheme,
                    createAxiomGeneratorContainerConfig.overflowChecks
                )
            )
        }

        fun BV(
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config
        ): LExpToSmtSetupInfo {
            val theory = when (createAxiomGeneratorContainerConfig.hashingScheme) {
                is HashingScheme.Legacy,
                HashingScheme.PlainInjectivity ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "BV")
                HashingScheme.Datatypes ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "DTBV")
            }
            return LExpToSmtSetupInfo(
                theory,
                createAxiomGeneratorContainerConfig.hashingScheme,
                CreateAxiomGeneratorContainer.HashArrayAxioms(createAxiomGeneratorContainerConfig),
                ExpNormalizer.create(
                    theory,
                    createAxiomGeneratorContainerConfig.hashingScheme,
                    createAxiomGeneratorContainerConfig.overflowChecks
                )
            )
        }

        fun UFNIA(
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config
        ): LExpToSmtSetupInfo {
            val theory = when (createAxiomGeneratorContainerConfig.hashingScheme) {
                is HashingScheme.Legacy,
                HashingScheme.PlainInjectivity ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "UFNIA")
                HashingScheme.Datatypes ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "UFDTNIA")
            }
            return LExpToSmtSetupInfo(
                theory,
                createAxiomGeneratorContainerConfig.hashingScheme,
                CreateAxiomGeneratorContainer.BwHashInstantiation(createAxiomGeneratorContainerConfig),
                ExpNormalizer.create(
                    theory,
                    createAxiomGeneratorContainerConfig.hashingScheme,
                    createAxiomGeneratorContainerConfig.overflowChecks,
                    { false }
                )
            )
        }

        fun UFPartialLIA(
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config,
            linearizationSelector: (LExpression) -> Boolean
        ): LExpToSmtSetupInfo {
            val theory = when (createAxiomGeneratorContainerConfig.hashingScheme) {
                is HashingScheme.Legacy,
                HashingScheme.PlainInjectivity ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "UFNIA")
                HashingScheme.Datatypes ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "UFDTNIA")
            }
            return LExpToSmtSetupInfo(
                theory,
                createAxiomGeneratorContainerConfig.hashingScheme,
                CreateAxiomGeneratorContainer.FullInstantiation(createAxiomGeneratorContainerConfig, linearizationSelector),
                ExpNormalizer.create(
                    theory,
                    createAxiomGeneratorContainerConfig.hashingScheme,
                    createAxiomGeneratorContainerConfig.overflowChecks,
                    linearizationSelector
                )
            )
        }

        fun UFLIA(
            useQuantifiers: Boolean,
            createAxiomGeneratorContainerConfig: CreateAxiomGeneratorContainer.Config
        ): LExpToSmtSetupInfo {
            val theory = when (createAxiomGeneratorContainerConfig.hashingScheme) {
                is HashingScheme.Legacy,
                HashingScheme.PlainInjectivity ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "UFLIA")
                HashingScheme.Datatypes ->
                    SmtTheory.fromString(SmtTheoryFeature.Quantifiers.smtlibAbbreviation(useQuantifiers) + "UFDTLIA")
            }
            return LExpToSmtSetupInfo(
                theory,
                createAxiomGeneratorContainerConfig.hashingScheme,
                CreateAxiomGeneratorContainer.FullInstantiation(createAxiomGeneratorContainerConfig),
                ExpNormalizer.create(
                    theory,
                    createAxiomGeneratorContainerConfig.hashingScheme,
                    createAxiomGeneratorContainerConfig.overflowChecks,
                    { true }
                )
            )
        }
    }
}

enum class SetupInfoType {
    UFBVorAUFBV,
    UFNIAorAUFNIA,
    UFLIAorAUFLIAPartial,
    UFLIAorAUFLIA
}
