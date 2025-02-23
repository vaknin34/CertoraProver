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

package vc.data.compilation.storage

import analysis.CommandWithRequiredDecls
import spec.cvlast.StorageBasis
import tac.Tag
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACKeyword
import vc.data.TACSymbol
import vc.data.compilation.storage.QuantifierGenerator.generateMapComparison

/**
 * A "simpler" version of the map comparisons, which encodes the comparisons directly
 * using quantifier expressions.
 *
 * An equality of a map `m1 == m2` is transformed into `
 * ```
 * forall i.m1[i] == m2[i]
 * ```
 * and an inequality is transformed into:
 * ```
 * exists i.m1[i] != m2[i]
 * ```
 *
 * With support as necessary for multiple parameters of different sorts, see [generateMapComparison].
 */
@InternalCVLCompilationAPI
internal object QuantifierGenerator : StorageComparisonDispatcher {
    /**
     * Generic version of map comparsions, given a list of parameter tags [pTypes] which are the domain
     * of the maps in [m1] and [m2], generated a forall/exist quantified expression binding variables
     * of the types in [pTypes] and then checking equality/inequality of [m1] and [m2] at those quantified
     * variables. The result of this comparison is placed in [outputVar].
     */
    private fun generateMapComparison(
        pTypes: List<Tag>,
        isEq: Boolean,
        m1: TACSymbol.Var,
        m2: TACSymbol.Var,
        outputVar: TACSymbol.Var
    ) : CommandWithRequiredDecls<TACCmd.Simple> {
        val witnesses = pTypes.mapIndexed {ind, ty ->
            TACKeyword.TMP(ty, "witness!$ind").toUnique("!")
        }
        val parameters = witnesses.map { it.asSym() }
        val equalityComparison = TACExpr.BinRel.Eq(
            TACExpr.Select.buildMultiDimSelect(
                m1.asSym(),
                parameters
            ),
            TACExpr.Select.buildMultiDimSelect(
                m2.asSym(),
                parameters
            )
        )
        val finalExp = if(isEq) {
            equalityComparison
        } else {
            TACExpr.UnaryExp.LNot(equalityComparison)
        }
        return CommandWithRequiredDecls(
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = outputVar,
                rhs = TACExpr.QuantifiedFormula(
                    isForall = isEq,
                    quantifiedVars = witnesses,
                    body = finalExp
                )
            ), m1, m2, outputVar
        )
    }

    override fun generateGhostMapComparison(
        eq: Boolean,
        output: TACSymbol.Var,
        fv1: Pair<String, TACSymbol.Var>,
        fv2: Pair<String, TACSymbol.Var>,
        storageBasis: StorageBasis.Ghost
    ): CommandWithRequiredDecls<TACCmd.Simple> {
        return generateMapComparison(
            isEq = eq,
            outputVar = output,
            m1 = fv1.second,
            m2 = fv2.second,
            pTypes = storageBasis.params.map { it.toTag() }
        )
    }

    override fun generateWordMapComparison(
        eq: Boolean,
        output: TACSymbol.Var,
        fv1: Pair<String, TACSymbol.Var>,
        fv2: Pair<String, TACSymbol.Var>,
        storageBasis: StorageBasis.VMStorageBasis
    ): CommandWithRequiredDecls<TACCmd.Simple> {
        return generateMapComparison(
            isEq = eq,
            pTypes = datastructures.stdcollections.listOf(Tag.Bit256),
            m1 = fv1.second,
            m2 = fv2.second,
            outputVar = output
        )
    }
}
