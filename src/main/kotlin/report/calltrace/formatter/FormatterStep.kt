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

@file:Suppress("IfThenToElvis")

package report.calltrace.formatter

import datastructures.NonEmptyList
import datastructures.stdcollections.*
import datastructures.toNonEmptyList
import report.BigIntPretty.bigIntPretty
import report.calltrace.HexOrDec
import report.calltrace.formatNumberLit
import report.checkWarn
import report.globalstate.logger
import rules.ContractInfo
import scene.ISceneIdentifiers
import solver.CounterexampleModel
import spec.cvlast.EVMBuiltinTypes.evmBitWidths
import utils.*
import vc.data.TACSymbol
import vc.data.state.TACValue
import java.math.BigInteger
import java.math.BigInteger.ONE
import java.math.BigInteger.ZERO

/**
 * The state of a value's formatting process and any additional context data (such as the value's type).
 * Any [FormatterStep] is allowed to mutate this data, and new variables may be added here as needed.
 * `val`s may also be changed to `var`, as needed.
 *
 * For example, [tv] is currently a `var` so that it is compatible with [UndoBoolReplacement].
 *
 * NOTE: steps should be designed as if they run in isolation.
 * In other words, a step is not allowed to depend on any state set by previous step(s).
 * This means the behavior of a step may not depend on the order in which the steps are executed,
 * nor should this behavior change if a step is removed.
 */
class ValueFormattingJob(var tv: TACValue, val type: FormatterType.Value<*>) {
    internal var contractName: String? = null
    internal var alternativeRepresentations: List<String> = emptyList()
    internal var tacValuePrettyPrint: String? = null

    init {
        checkWarn(tv != TACValue.Uninitialized) {
            "ValueFormattingJob should not get an uninitialized value (it only lists a list of representations but " +
                "cannot do the Sarif-wrapping that should be done in that case)"
        }
    }

    /** applies the steps (in reverse order) and returns the final representation of the string */
    internal fun finish(): NonEmptyList<String>  {
        val res = mutableListOf<String>()

        /** s -> "$s ($description_0) ($description_1) ... ($description_n)" */
        for (description in alternativeRepresentations) {
            res += description
        }

        /** s -> "$contractName (s)" */
        if (contractName != null) {
            checkWarn(res.size == 1) { "expecting this to be an address, we currently only give 1 representation there" }
            val r = "$contractName (${res.removeFirst()})"
            res += r
        }
        return res.toNonEmptyList() ?: error("should have at least one value in the list (formatting value \"$tv\"")
    }
}

fun interface FormatterStep {
    /** apply this step to [job] by mutating it */
    fun execute(job: ValueFormattingJob)
}

/**
 * Adds the name to values which are addresses of known contracts.
 * for each (non pre-compiled) contract in [scene], [modelAddrToContractName] maps the model's
 * chosen address for that contract to the [ContractInfo] of that address.
 *
 * [scene] will be used in the future to recognize pre-compiled contracts (CERT-1917)
 */
@Suppress("UNUSED_PARAMETER")
class ContractNames(modelAddrToContractInfo: Map<TACValue.PrimitiveValue.Integer, ContractInfo>, scene: ISceneIdentifiers) : FormatterStep {
    private val modelAddrToContractName: Map<BigInteger, String> =
        modelAddrToContractInfo
            .entries
            .associate { (tv, info) -> tv.asBigInt to info.name }

    private fun contractAddr(tv: TACValue, type: FormatterType.Value<*>?): BigInteger? =
        if (tv is TACValue.PrimitiveValue.Integer && type?.toMeta() is ValueMeta.Address) {
            tv.asBigInt
        } else {
            null
        }

    override fun execute(job: ValueFormattingJob) {
        val addr = contractAddr(job.tv, job.type)
        val contractName = modelAddrToContractName[addr]

        if (contractName != null) {
            job.contractName = contractName
        }
    }
}

/** Fill the list of alternative representations for a given value (to be cycled through by the users). */
object AlternativeRepresentations : FormatterStep {

    private val shortHands: Map<BigInteger, MutableList<OptionalDescription>>

    init {
        shortHands = mutableMapOf()

        fun add(value: BigInteger, desc: String, condition: (ValueMeta?) -> Boolean) {
            val vd = OptionalDescription(desc, condition)
            shortHands
                .getOrPut(value) { mutableListOf() }
                .add(vd)
        }

        for (bitWidth in evmBitWidths) {
            add(powerOfTwoMinusOne(bitWidth), "MAX_UINT$bitWidth") { it is ValueMeta.UIntK && it.bitwidth == bitWidth }

            add(powerOfTwoMinusOne(bitWidth - 1), "MAX_INT$bitWidth") { it is ValueMeta.SignedIntK && it.bitwidth == bitWidth }
            add(powerOfTwo(bitWidth - 1).negate(), "MIN_INT$bitWidth") { it is ValueMeta.SignedIntK && it.bitwidth == bitWidth }

            add(powerOfTwo(bitWidth), "2^$bitWidth") { it is ValueMeta.Mathint }
            add(powerOfTwo(bitWidth).negate(), "-(2^$bitWidth)") { it is ValueMeta.Mathint }
        }

        // would be dead code now, and I'm not sure how useful the shorthand is
        // add(powerOfTwoMinusOne(EVM_ADDRESS_SIZE), "MAX_EVM_ADDRESS") { it is ValueMeta.Address }
    }

    /** This whole mechanism is overlapping with [BigInteger.prettyString], however it takes into account ValueMeta, so
     * it's not subsumed by it. Just keeping it for now -- we can play with these representations later. */
    private fun matchingDescriptions(rawValue: BigInteger, meta: ValueMeta?) =
        shortHands[rawValue]
            ?.filter { it.condition(meta) }
            ?.map { it.description }?.firstOrNull()

    enum class Representations(val shortName: String, val example: String /*, val convert: (BigInteger, ValueMeta?) -> String*/) {
        Pretty("STR", "2^8-1 (MAX_UINT8)"),
        Decimal("DEC", "255") ,
        Hex("HEX", "0xff"),
        ;
    }

    private data class OptionalDescription(val description: String, val condition: (ValueMeta?) -> Boolean)


    private fun computeRepresentations(job: ValueFormattingJob): List<String> {
        checkWarn(job.tacValuePrettyPrint != null) { "tacValuePrettyPrint needs to be set at this point, but is `null`" }
        val default = listOf(job.tacValuePrettyPrint!!)
        return when (job.type) {
            is FormatterType.Value.Unknown -> default
            is FormatterType.Value.CVL,
            is FormatterType.Value.EVM -> {
                val bigInt = job.tv.asBigIntOrNull()
                if (job.type.isAddress
                    || job.type.isBool
                    || job.type.isBytes
                    || bigInt == null) {
                    default
                } else {
                    // XXX we're ignoring job.tacValuePrettyPrint here -- so, assumption is that in this branch
                    // the representations from Representations.values() supersede it -- we might consider merging the
                    // two case, or separate them more thoroughly ..
                    Representations.values().map {
                        when (it) {
                            Representations.Pretty -> {
                                val numeric = job.tacValuePrettyPrint ?: bigInt.toHexString()
                                val strRep = (matchingDescriptions(bigInt, job.type.toMeta()) ?: bigIntPretty(bigInt))
                                numeric + (strRep?.let { " ($strRep)" }.orEmpty())
                            }
                            Representations.Decimal -> bigInt.toString(10)
                            Representations.Hex -> bigInt.toHexString()
                        }
                    }
                }
            }
        }
    }

    override fun execute(job: ValueFormattingJob) {
        job.alternativeRepresentations = computeRepresentations(job)
    }
}

/** Prints a value based on its [TACValue]. Set [ValueFormattingJob.tacValuePrettyPrint]. */
class PrettyPrintTACValue(private val model: CounterexampleModel) : FormatterStep {
    private fun ValueMeta.Enum.format(ordinal: BigInteger): String {
        /** We're using the value emitted from the SMT as an array index, so we must validate it */
        val nameOfLiteral = ordinal.toIntOrNull()?.let { idx -> elements.getOrNull(idx) }

        return if (nameOfLiteral != null) {
            "$name.$nameOfLiteral"
        } else {
            "$name($ordinal)"
        }
    }

    override fun execute(job: ValueFormattingJob) {
        val type = job.type
        val tv = job.tv

        job.tacValuePrettyPrint = when (tv) {
            is TACValue.PrimitiveValue -> {
                val num = tv.asBigInt
                val meta = job.type.toMeta()

                if (meta is ValueMeta.Enum) {
                    meta.format(num)
                } else if (meta is ValueMeta.Boolean || tv is TACValue.PrimitiveValue.Bool) {
                    /** XXX: can we can ensure booleans get assigned to [TACValue.PrimitiveValue.Bool]? */
                    val b = num != ZERO
                    b.toString()
                } else {
                    val style = if (meta is ValueMeta.Bytes) { HexOrDec.ALWAYS_HEX } else { HexOrDec.HEX_IF_ABOVE_DEC_LIMIT }
                    num.normalizeRepresentation(type)?.let { normalized -> formatNumberLit(normalized, style) }
                }
            }

            // (alex n:) `job.tv is TACValue.Skey` is actually not the right criterion for this case.
            //  See the other usages of CounterExampleModel.storageKeyToInteger for the right criterion.
            //  (There it was somewhat easy to do, but here we're missing the type of the tac expression whose model
            //  we're printing unfortunately.)
            //  (background: in the Legacy hashing scheme case, we should use the value of `from_skey(x)` rather than
            //  `x`, just like in the Datatypes case, and then we'll see a TACValue...Integer here)
            is TACValue.SKey -> {
                model
                    .storageKeyToInteger(tv)
                    .mapLeft { integer -> integer.toString() }
                    .leftOrElse { err ->
                        logger.warn { "while formatting $tv: expected hashable SKey, got $err" }
                        null
                    }
            }

            else -> null
        }
    }


}

/**
 * bv256s are allowed to be optimized to booleans.
 * this should be opaque to the user, and the call trace should format using the original type.
 *
 * for example, an expression like `foo(1)` for some internal `function foo(uint256 n)`
 * may have had its parameter replaced with a boolean, changing its string representation to `foo(true)`,
 * which we don't want here.
 *
 * this step un-replaces the value with an integer.
 */
class UndoBoolReplacement(programVars: Iterable<TACSymbol.Var>, model: CounterexampleModel) : FormatterStep {
    init {
        unused(programVars)
        unused(model)
    }
    // XXX (alex n) many program variables can get the same model value - I don't see how this is correct (?)..
    // private val wasReplaced = programVars
    //     .filter { it.meta.contains(TACMeta.REPLACED_WITH_BOOL) }
    //     .mapNotNullToSet(model::valueAsTACValue)

    override fun execute(job: ValueFormattingJob) {
        val tv = job.tv
        if (tv is TACValue.PrimitiveValue.Bool && !job.type.isBool) {
            job.tv = TACValue.PrimitiveValue.Integer(tv.value.toBigInteger())
        }
    }
}

fun BigInteger.toHexString() =
    if (this.signum() >= 0) {
        "0x" + this.toString(16)
    } else {
        "-0x" + this.negate().toString(16)
    }

private fun powerOfTwo(exp: Int) = ONE.shl(exp)
private fun powerOfTwoMinusOne(exp: Int) = ONE.shl(exp).minus(ONE)
