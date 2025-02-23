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

package analysis.opt.numeric

import analysis.CmdPointer
import analysis.numeric.ConditionQualifier
import analysis.numeric.LogicalConnectiveQualifier
import analysis.numeric.Qualifier
import analysis.numeric.VariableSaturation
import com.certora.collect.*
import datastructures.stdcollections.*
import vc.data.TACSymbol


/**
 * Qualifiers which are atomic, weakly relational dataflow facts that are attached to variables. Often records
 * some symbolic information, but makes no attempt to do any sort of semantic reasoning.
 *
 * To save space, we often will omit "the value with this qualifier represents..." and instead say "this value represents".
 */
sealed class VROQuals : Qualifier<VROQuals> {

    abstract val related: TreapSet<TACSymbol.Var>

    override fun relates(v: TACSymbol.Var) = v in related

    /**
     * A value annotated with this qualifier holds the result of [op1] [condition] [op2], where [condition] is
     * <=, !=, etc.
     */
    data class Condition(
        override val op1: TACSymbol,
        override val op2: TACSymbol,
        override val condition: ConditionQualifier.Condition
    ) : VROQuals(), ConditionQualifier, Flippable {
        override val related = treapSetOfNotNull(op1 as? TACSymbol.Var, op2 as? TACSymbol.Var)

        override fun flip(): VROQuals = ConditionQualifier.flip(this, ::Condition)
    }

    /**
     * This value holds the result of masking [op] with `2^[bitWidth]-1`
     */
    data class MaskedOf(val op: TACSymbol.Var, val bitWidth: Int) : VROQuals() {
        override val related = treapSetOf(op)
    }

    /**
     * This value can be safely negated for a bitwidth of [extendedBit], i.e.,
     * the value must not hold the minimum negative value for a bitwidth.
     */
    data class Negatable(val extendedBit: Int) : VROQuals() {
        override val related = treapSetOf<TACSymbol.Var>()
    }

    /**
     * A [LogicalConnectiveQualifier], which indices that f([op1]) [connective] f([op2]),
     * where f is defined to be `\b.b` if [applyNot] is false, `\b.!b` if it is true.
     *
     * This trick let's us "flip" these logical connectives without eagerly propagating information to [op1] and [op2],
     * we simply record that when interpreting any conditional information in [op1] and [op2], we should "flip" (or apply not)
     * to those results.
     */
    data class LogicalConnective(
        override val op1: TACSymbol.Var,
        override val op2: TACSymbol.Var,
        override val connective: LogicalConnectiveQualifier.LBinOp,
        override val applyNot: Boolean
    ) : VROQuals(), LogicalConnectiveQualifier, Flippable {
        constructor(connective: LogicalConnectiveQualifier.LBinOp, op1: TACSymbol.Var, op2: TACSymbol.Var) : this(
            op1, op2, connective, false
        )

        override val related = treapSetOf(op1, op2)

        override fun flip(): VROQuals = LogicalConnectiveQualifier.flip(this, ::LogicalConnective)
    }

    /**
     * This value must be equal to the value [other]. This is used instead of eagerly saturating qualifiers,
     * when we know we have variables of "interest", we will fully saturate with these qualifiers, and then
     * use the qualifiers of those families.
     */
    data class MustEqual(val other: TACSymbol.Var) : VROQuals() {
        override val related = treapSetOf(other)
    }

    data class MustNotEqual(val other: TACSymbol.Var) : VROQuals() {
        override val related = treapSetOf(other)
    }

    /**
     * This value has [lowerBound] as a weak lower bound. That is, a value `v` with this qualifier must satisfy:
     * [lowerBound] <= v
     */
    data class WeakLowerBound(val lowerBound: TACSymbol) : VROQuals() {
        override val related = treapSetOfNotNull(lowerBound as? TACSymbol.Var)
    }


    sealed class MultPostProcess {
        abstract val opPointer: CmdPointer

        /**
         * Indicates the multiplication was sign extended from [BitExtension.extendedBit]
         * at the location [BitExtension.extensionPointer].
         */
        data class BitExtension(val extensionPointer: CmdPointer, val extendedBit: Int) : MultPostProcess() {
            override val opPointer: CmdPointer
                get() = extensionPointer
        }

        /**
         * Indicates the multiplication was masked to be within the bitwidth [maskBit].
         */
        data class Masking(override val opPointer: CmdPointer, val maskBit: Int) : MultPostProcess()
    }


    /**
     * Common marker for qualifiers that record symbolic multiplication information,
     * that is, values with this qualifier represent [op1] * [op2], performed at [where].
     *
     * [postProcess], if non-null, means that this value was also post processed at
     * [MultPostProcess.opPointer]. This operation can be a sign extension or a masking,
     * depending on the subclass of [MultPostProcess].
     */
    sealed interface MultiplicationMarker {
        val op1: TACSymbol
        val op2: TACSymbol
        val postProcess: MultPostProcess?
        val where: CmdPointer
    }

    /**
     * Plain version of [MultiplicationMarker], with no sign extension information.
     *
     * Q: Can this be folded into the [SignExtendedOfMultiplication] or [MaskOfMultiplication]?
     * A: Yes, the value [postProcess] tells you whether or not there was a sign extension or mask. I prefer
     * keeping the separate classes as that feels "cleaner".
     */
    data class MultiplicationOf(
        override val op1: TACSymbol,
        override val op2: TACSymbol,
        override val where: CmdPointer
    ) : VROQuals(), MultiplicationMarker {
        override val related = treapSetOfNotNull(op1 as? TACSymbol.Var, op2 as? TACSymbol.Var)

        override val postProcess: MultPostProcess?
            get() = null
    }

    /**
     * Variant of [MultiplicationMarker] where the multiplication has been masked
     * at [maskLocation] to be within the bound [maskBit].
     */
    data class MaskOfMultiplication(
        val multiplicationSource: CmdPointer,
        override val op1: TACSymbol,
        override val op2: TACSymbol,
        val maskBit: Int,
        val maskLocation: CmdPointer,
    ) : MultiplicationMarker, VROQuals() {
        override val postProcess: MultPostProcess.Masking
            get() = MultPostProcess.Masking(opPointer = maskLocation, maskBit)
        override val where: CmdPointer
            get() = multiplicationSource

        override val related = treapSetOfNotNull(op1 as? TACSymbol.Var, op2 as? TACSymbol.Var)
    }

    /**
     * Variant of [MultiplicationMarker] where the multiplication has been sign extended
     * at [signExtension] from bit [extendedBit].
     */
    data class SignExtendedOfMultiplication(
        val extendedBit: Int,
        override val op1: TACSymbol,
        override val op2: TACSymbol,
        val signExtension: CmdPointer,
        val sourceMultiplication: CmdPointer
    ) : VROQuals(), MultiplicationMarker {
        override val related = treapSetOfNotNull(op1 as? TACSymbol.Var, op2 as? TACSymbol.Var)

        override val postProcess: MultPostProcess.BitExtension
            get() = MultPostProcess.BitExtension(signExtension, extendedBit)

        override val where: CmdPointer
            get() = sourceMultiplication
    }

    /**
     * Indicates that this value is the result of sign extending some other value (which is
     * not recorded in this qualifier) from bit [extendedBit]. Used to detect redundant sign extensions.
     */
    data class SignExtended(
        val extendedBit: Int // counting from the LSB, which is given index 0
    ) : VROQuals() {
        override val related = treapSetOf<TACSymbol.Var>()
    }


    override fun saturateWith(equivClasses: VariableSaturation): List<VROQuals> =
        listOf(this)
}
