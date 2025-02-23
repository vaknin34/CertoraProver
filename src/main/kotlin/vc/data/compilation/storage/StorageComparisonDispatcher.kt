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
import spec.cvlast.GhostSort
import spec.cvlast.StorageBasis
import spec.cvlast.SupportsScalarComparison
import tac.Tag
import vc.data.*

/**
 * A common helper interface for generating storage comparisons for individual components.
 * It handles the basic case for scalar comparisons (when the type of the values being compared
 * of [tac.Tag.UserDefined.UninterpretedSort], [Tag.Int], [Tag.Bool], or [Tag.Bit256]) including
 * generating snippets.
 *
 * In the case of the maps being word or ghost maps, it dispatches to the specific map strategy implemented
 * by overriders via [generateGhostMapComparison] and [generateWordMapComparison]. The two implemented strategies are
 * skolemization (in [SkolemizationGenerator]) or quantification ([QuantifierGenerator]). The latter is more general
 * (and indeed, behind the scenes, the [SkolemizationGenerator] is just doing the skolemization which would be
 * done by the quantifier grounding), but the skolemization version currently gives nicer counter examples. Once
 * quantifier counter example generation works in general, there is no need for the two strategies.
 */
@InternalCVLCompilationAPI
internal interface StorageComparisonDispatcher {
    /**
     * Generate an equality of inequality comparison (depending on the value of [isEq])
     * placing the result in [output]. The components being compared are represented in [fv1] and [fv2].
     * The first component of each pair indicates the CVL name of the storage variables being compared, whereas
     * the second component is the scalarized storage slot, the ghost variable, (potentially split/unpacked) wordmap
     * component of storage, a balances map, or a ghost map/function.
     *
     * The "role" of the components being compared is recorded in [storageBasis], e.g., whether the wordmaps
     * are part of contract storage, vs the balances, etc.
     */
    fun generateComparison(
        isEq: Boolean,
        output: TACSymbol.Var,
        fv1: Pair<String, TACSymbol.Var>,
        fv2: Pair<String, TACSymbol.Var>,
        storageBasis: StorageBasis
    ) : CommandWithRequiredDecls<TACCmd.Simple> {
        val v1 = fv1.second
        val v2 = fv2.second
        check(output.tag == Tag.Bool)
        require(v1.tag == v2.tag)
        return when(v1.tag) {
            is Tag.UserDefined.UninterpretedSort,
            Tag.Int,
            is Tag.Bits,
            Tag.Bool -> {
                generateScalarComparison(isEq, storageBasis, output, fv1, fv2)
            }
            Tag.WordMap -> {
                generateWordMapComparison(isEq, output, fv1, fv2,
                    storageBasis as StorageBasis.VMStorageBasis
                )
            }
            is Tag.GhostMap -> {
                check(storageBasis is StorageBasis.Ghost) {
                    "Tag ${v1.tag} is not expected for basis $storageBasis"
                }
                generateGhostMapComparison(isEq, output, fv1, fv2, storageBasis)
            }
            is Tag.TransientTag -> throw UnsupportedOperationException("Transient tags are not possible in storage state")
            Tag.ByteMap -> throw UnsupportedOperationException("Tag ${v1.tag} is not expected for basis $storageBasis")
        }
    }

    private fun generateScalarComparison(
        isEq: Boolean,
        storageBasis: StorageBasis,
        output: TACSymbol.Var,
        fv1: Pair<String, TACSymbol.Var>,
        fv2: Pair<String, TACSymbol.Var>
    ): CommandWithRequiredDecls<TACCmd.Simple> {
        val v1 = fv1.second
        val v2 = fv2.second
        check(!isEq || storageBasis is SupportsScalarComparison) {
            "Expected that an equality assertion over scalars would be " +
                "for a basis that supports scalar comparisons, got $storageBasis"
        }
        val eqTarget = if (isEq) {
            output
        } else {
            TACKeyword.TMP(Tag.Bool, "!toNegate").toUnique("!")
        }
        val ret = mutableListOf<TACCmd.Simple>(
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = eqTarget,
                rhs = TACExpr.BinRel.Eq(v1.asSym(), v2.asSym())
            )
        )
        if (!isEq) {
            ret.add(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = output,
                    rhs = TACExpr.UnaryExp.LNot(eqTarget.asSym())
                )
            )
        }
        if (isEq) {
            /**
             * We can provide witness information for equality checks
             */
            check(storageBasis is SupportsScalarComparison)
            ret.add(
                storageBasis.toSnippet(
                    output,
                    p1 = fv1.first to v1,
                    p2 = fv2.first to v2,
                ).toAnnotation()
            )
        }
        return CommandWithRequiredDecls(ret, output, eqTarget, v1, v2)
    }

    fun generateGhostMapComparison(
        eq: Boolean,
        output: TACSymbol.Var,
        fv1: Pair<String, TACSymbol.Var>,
        fv2: Pair<String, TACSymbol.Var>,
        storageBasis: StorageBasis.Ghost
    ): CommandWithRequiredDecls<TACCmd.Simple>

    fun generateWordMapComparison(
        eq: Boolean,
        output: TACSymbol.Var,
        fv1: Pair<String, TACSymbol.Var>,
        fv2: Pair<String, TACSymbol.Var>,
        storageBasis: StorageBasis.VMStorageBasis
    ) : CommandWithRequiredDecls<TACCmd.Simple>

    /**
     * This and the following functions generate snippets for comparison of scalar values, whether
     * they come from storage [spec.cvlast.StorageBasis.ContractClass] or
     * a ghost [spec.cvlast.StorageBasis.Ghost]
     */
    private fun SupportsScalarComparison.toSnippet(
        output: TACSymbol.Var,
        p1: Pair<String, TACSymbol.Var>,
        p2: Pair<String, TACSymbol.Var>
    ) : SnippetCmd.CVLSnippetCmd {
        return when(this) {
            is StorageBasis.ContractClass -> this.toSnippet(output, p1, p2)
            is StorageBasis.Ghost -> this.toSnippet(output, p1, p2)
        }
    }

    private fun StorageBasis.ContractClass.toSnippet(
        output: TACSymbol.Var,
        p1: Pair<String, TACSymbol.Var>,
        p2: Pair<String, TACSymbol.Var>
    ): SnippetCmd.CVLSnippetCmd {
        return SnippetCmd.CVLSnippetCmd.ScalarStorageComparison(
            basis = this,
            resultSymbol = output,
            p1 = p1,
            p2 = p2,
            typeValue = p1.second.meta.find(TACMeta.STORAGE_TYPE)
        )
    }


    private fun StorageBasis.Ghost.toSnippet(
        output: TACSymbol.Var,
        p1: Pair<String, TACSymbol.Var>,
        p2: Pair<String, TACSymbol.Var>
    ): SnippetCmd.CVLSnippetCmd {
        check(output.tag == Tag.Bool) {
            "Unexpected result type for snippet for scalar ghost"
        }
        check(this.params.isEmpty() && (this.sort == GhostSort.Variable || this.sort == GhostSort.Function)) {
            "Attempting to output a scalar ghost snippet for $this, but it is not a variable or function or it has multiple parameters??"
        }
        return SnippetCmd.CVLSnippetCmd.ScalarGhostComparison(
            resultSymbol = output,
            p1 = p1,
            p2 = p2,
            basis = this,
            sort = this.sort
        )
    }
}
