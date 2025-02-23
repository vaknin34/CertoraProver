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

package smtlibutils.externalsolvers.mathematica

import smtlibutils.algorithms.TransformSmt
import smtlibutils.data.*

data class ArithmeticIR(
    val constraints: Set<Set<Constraint>>,
    val mode: Mode,
    val qualIdSanitizer: QualIdMathematicaSanitizer
) {

    enum class Mode {
        CNF, DNF;
    }

    class QualIdMathematicaSanitizer(
        val charFilter: Regex = Regex("[^A-Za-z0-9]"),
        override val smtScript: ISmtScript = SmtScript(),
    ) : TransformSmt<Unit>() {

        val sanitizedIdToOrigQualId: MutableMap<String, SmtExp.QualIdentifier> = mutableMapOf()

        override fun qualId(exp: SmtExp.QualIdentifier, acc: Unit): SmtExp.QualIdentifier {
            val sanitizedId = exp.id.sym.replace(charFilter, "")
            check(sanitizedIdToOrigQualId[sanitizedId] == null || sanitizedIdToOrigQualId[sanitizedId] == exp) { "Collision of the sanitized identifier ${sanitizedId}: maps to both ${exp} and ${sanitizedIdToOrigQualId[sanitizedId]}" }
            if (sanitizedIdToOrigQualId[sanitizedId] == null) sanitizedIdToOrigQualId[sanitizedId] = exp
            return smtScript.qualIdentifier(
                smtScript.simpleIdentifier(sanitizedId),
                exp.qualification,
                exp.sort
            )
        }
    }

    sealed class Constraint(open val lhs: SmtExp, open val rhs: SmtExp) {

        data class Equation(val polarity: Boolean, override val lhs: SmtExp, override val rhs: SmtExp) :
            Constraint(lhs, rhs)

        /** lhs <(=) rhs */
        data class InEquation(val isStrict: Boolean, override val lhs: SmtExp, override val rhs: SmtExp) :
            Constraint(lhs, rhs)

        data class BooleanVariable(
            val polarity: Boolean,
            override val lhs: SmtExp.QualIdentifier,
            override val rhs: SmtExp.BoolLiteral
        ) : Constraint(lhs, rhs)
    }

    companion object {

        fun fromDnfOrCnf(
            dnfOrCnf: Set<Set<SmtExp>>,
            mode: Mode,
            qualIdSanitizer: QualIdMathematicaSanitizer = QualIdMathematicaSanitizer()
        ): ArithmeticIR =
            ArithmeticIR(
                dnfOrCnf.map {
                    fromCubeOrClauseUtil(
                        it,
                        qualIdSanitizer
                    )
                }.toSet(),
                mode,
                qualIdSanitizer
            )

        fun fromCubeOrClause(
            c: Set<SmtExp>,
            mode: Mode = Mode.DNF,
            qualIdSanitizer: QualIdMathematicaSanitizer = QualIdMathematicaSanitizer()
        ): ArithmeticIR =
            ArithmeticIR(
                setOf(
                    fromCubeOrClauseUtil(
                        c,
                        qualIdSanitizer
                    )
                ), mode, qualIdSanitizer
            )

        private fun fromCubeOrClauseUtil(c: Set<SmtExp>, qualIdSanitizer: QualIdMathematicaSanitizer): Set<Constraint> {
            val constraints = mutableSetOf<Constraint>()
            c.forEach { lit ->
                assert(lit.isBooleanLiteral())
                val polarity = !lit.isAtom()
                val atom = if (polarity) (lit as SmtExp.Apply).args[0] else lit

                when (atom) {
                    is SmtExp.QualIdentifier -> {
                        check(atom.sort == Sort.BoolSort) { "unexpected variable/constant; $this ; $lit" }
                        constraints.add(
                            Constraint.BooleanVariable(
                                polarity,
                                qualIdSanitizer.qualId(atom, Unit),
                                qualIdSanitizer.smtScript.boolLit(false)
                            )
                        )
                    }
                    is SmtExp.Apply -> {
                        check(atom.args.size == 2)
                        val lhs = qualIdSanitizer.expr(atom.args[0], Unit)
                        val rhs = qualIdSanitizer.expr(atom.args[1], Unit)
                        when (atom.fs) {
                            is SmtIntpFunctionSymbol.Core.Eq -> constraints.add(
                                Constraint.Equation(
                                    polarity,
                                    lhs,
                                    rhs
                                )
                            )
                            SmtIntpFunctionSymbol.IRA.Ge(Sort.IntSort) -> constraints.add(
                                if (polarity) Constraint.InEquation(
                                    true,
                                    lhs,
                                    rhs
                                ) else Constraint.InEquation(
                                    false,
                                    rhs,
                                    lhs
                                )
                            )
                            SmtIntpFunctionSymbol.IRA.Gt(Sort.IntSort) -> constraints.add(
                                if (polarity) Constraint.InEquation(
                                    false,
                                    lhs,
                                    rhs
                                ) else Constraint.InEquation(
                                    true,
                                    rhs,
                                    lhs
                                )
                            )
                            SmtIntpFunctionSymbol.IRA.Le(Sort.IntSort) -> constraints.add(
                                if (polarity) Constraint.InEquation(
                                    true,
                                    rhs,
                                    lhs
                                ) else Constraint.InEquation(
                                    false,
                                    lhs,
                                    rhs
                                )
                            )
                            SmtIntpFunctionSymbol.IRA.Lt(Sort.IntSort) -> constraints.add(
                                if (polarity) Constraint.InEquation(
                                    false,
                                    rhs,
                                    lhs
                                ) else Constraint.InEquation(
                                    true,
                                    lhs,
                                    rhs
                                )
                            )
                            is SmtIntpFunctionSymbol.Core.Distinct -> error("distinct not allowed here (use a normal form conversion like NNF first), $lit")
                            else -> error("unexpected function symbol; $this ; $lit")
                        }
                    }
                    is SmtExp.BoolLiteral -> error("unexpected boolean literal; $this ; $lit")
                    else -> error("unexpected case; $this ; $lit")
                }
            }
            return constraints
        }
    }
}