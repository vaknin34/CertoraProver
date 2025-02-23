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

package smtlibutils.statistics

import evm.MAX_EVM_INT256
import kotlinx.coroutines.flow.*
import smtlibutils.algorithms.TraverseSmt
import smtlibutils.cmdprocessor.*
import smtlibutils.data.*
import utils.*
import java.util.*
import kotlin.Comparator

/**
 * A [CmdProcessor] that collects some stats on an [SMT] object.
 * The idea is to give a quick summary using some, admittedly very rough, metrics, like "how many asserts,
 * multiplications, divisions, uninterp_bwands, etc. are we seeing").
 * Also allows for some pattern matching (not the fastest, but hopefully easy to use by just writing [SmtExp]s).
 */
class CollectStatsCmdProc(
    override val solverInstanceInfo: SolverInstanceInfo,
    override val options: CmdProcessor.Options,
    val smtScript: SmtScript
) : CmdProcessor {

    companion object {
        suspend fun countSmt(smt: SMT): List<Counter<*>> {
            val script = SmtScript()
            val sorted = Sorter(script).smt(smt)

            val proc = CollectStatsCmdProc(
                SolverInstanceInfo.None,
                CmdProcessor.Options.DontCare,
                script,
            )
            sorted.cmds.forEach { proc.process(it) }

            return listOf(
                proc.cmdOccurrences,
                proc.fsOccurrences,
                proc.okVarDefOccurrences,
                proc.signedIntOpOccurrences
            )
        }
    }

    class Counter<T>(val name: String, comp: Comparator<T>) {

        val m: SortedMap<T, Int> = TreeMap(comp)

        fun increment(t: T) {
            m.computeIfAbsent(t) { 0 }
            m[t] = m[t]!! + 1
        }

        fun toCounterData() = CounterData(name, m.mapKeys { (k, _) -> k.toString() })

        override fun toString(): String {
            return "$name\n  ${m.entries.joinToString("\n  ") { (key, value) -> "$key: $value" }}"
        }
    }

    data class CounterData(val name: String, val entryToCounter: Map<String, Int>) {
        val headers get() = entryToCounter.keys
    }

    private val fsComparator = Comparator<FsTypes> { p0, p1 -> p0.toString().compareTo(p1.toString()) }
    val fsOccurrences: Counter<FsTypes> = Counter("function symbols", fsComparator)

    private val signedIntOpComparator =
        Comparator<SignedIntOpTypes> { p0, p1 -> p0.toString().compareTo(p1.toString()) }
    val signedIntOpOccurrences: Counter<SignedIntOpTypes> = Counter("signed int ops", signedIntOpComparator)

    private val cmdComparator = Comparator<Any> { p0, p1 -> p0.toString().compareTo(p1.toString()) }
    val cmdOccurrences: Counter<Any> = Counter("commands by type", cmdComparator)

    private val okVarDefComparator = Comparator<OkVarType> { p0, p1 -> p0.toString().compareTo(p1.toString()) }
    val okVarDefOccurrences: Counter<OkVarType> = Counter("okVarDefs", okVarDefComparator)

    private fun countOkVarDefIfApplicable(exp: SmtExp) {
        if (exp !is SmtExp.Apply.Binary) return
        if (exp.fs !is SmtIntpFunctionSymbol.Core.Eq) return

        val lhs = exp.args.first()
        if (lhs !is SmtExp.QualIdentifier) return

        if (!lhs.id.sym.startsWith("OK_")) return

        okVarDefOccurrences.increment(OkVarType)
    }

    private val assertExpTraversal = object : TraverseSmt() {
        override val script = smtScript

        override fun apply(exp: SmtExp.Apply) {
            fsOccurrences.increment(FsTypes.fromFs(exp.fs))
            SignedIntOpTypes.Comp.patterns.forEach {
                if (SmtExp.Unification(script).unify(exp, it) != null) {
                    signedIntOpOccurrences.increment(SignedIntOpTypes.Comp)
                }
            }
            SignedIntOpTypes.PositiveSignedDet.patterns.forEach {
                if (SmtExp.Unification(script).unify(exp, it) != null) {
                    signedIntOpOccurrences.increment(SignedIntOpTypes.PositiveSignedDet)
                }
            }
            SignedIntOpTypes.NegativeSignedDet.patterns.forEach {
                if (SmtExp.Unification(script).unify(exp, it) != null) {
                    signedIntOpOccurrences.increment(SignedIntOpTypes.NegativeSignedDet)
                }
            }
            super.apply(exp)
        }

        override fun intLit(exp: SmtExp.IntLiteral) {
            SignedIntOpTypes.MaxSInt.patterns.forEach {
                if (SmtExp.Unification(script).unify(exp, it) != null) {
                    signedIntOpOccurrences.increment(SignedIntOpTypes.MaxSInt)
                }
            }
            super.intLit(exp)
        }
    }

    override fun processResult(cmd: Cmd) = flow<String> {
        cmdOccurrences.increment(cmd.javaClass.simpleName)
        when (cmd) {
            is Cmd.Assert -> {
                processAssertedExp(cmd.exp)
            }
            else -> {
                /* do nothing */
            }
        }
    }

    private fun processAssertedExp(exp: SmtExp) {
        assertExpTraversal.expr(exp)
        countOkVarDefIfApplicable(exp)
    }

    override fun close() {
        /** do nothing */
    }

}


/**
 * Used to group function symbols in the resulting overview -- e.g. all `slct_` function symbols will be shown in one
 * column.
 *
 * Note: Hm, actually this grouping could be done as a relational algebra-style table operation after-the-fact...
 *   some day... perhaps ...
 */
sealed class FsTypes(val actualFs: SmtFunctionSymbol) {
    class Slct(fs: SmtUnintpFunctionSymbol) : FsTypes(fs) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false
            return true
        }

        override fun hashCode(): Int {
            return javaClass.hashCode()
        }

        override fun toString(): String = "slct"
    }

    data class OtherUnintp(val fs: SmtUnintpFunctionSymbol) : FsTypes(fs) {
        override fun toString(): String = fs.name.toString()
    }

    data class Intp(val fs: SmtIntpFunctionSymbol) : FsTypes(fs) {
        override fun toString(): String = fs.name.toString()
    }

    companion object {
        fun fromFs(fs: SmtFunctionSymbol): FsTypes =
            when (fs) {
                is SmtUnintpFunctionSymbol ->
                    if (fs.name.sym.startsWith("slct_")) {
                        Slct(fs)
                    } else {
                        OtherUnintp(fs)
                    }
                is SmtIntpFunctionSymbol ->
                    Intp(fs)
                else -> `impossible!`
            }
    }
}


/**
 * show all ok vars in one column
 */
object OkVarType {
    override fun toString(): String {
        return "OK_Var"
    }

}

/**
 * Uses pattern matching (via unification) to detect some patterns (doesn't work too well, so far, but has room for
 * improvement, I think).
 */
sealed class SignedIntOpTypes {
    object Comp : SignedIntOpTypes() {
        override fun toString(): String {
            return "signed_comparison"
        }

        val patterns = listOf(
            SmtPatterns.sLePattern
        )
    }

    object PositiveSignedDet : SignedIntOpTypes() {
        override fun toString(): String {
            return "is_positive_sint"
        }

        val patterns = listOf(
            SmtPatterns.isPositiveSignedIntPattern(SmtExp.PlaceHolder("x", Sort.IntSort))
        )
    }

    object NegativeSignedDet : SignedIntOpTypes() {
        override fun toString(): String {
            return "is_negative_sint"
        }

        val patterns = listOf(
            SmtPatterns.isPositiveSignedIntPattern(SmtExp.PlaceHolder("x", Sort.IntSort))
        )
    }

    object MaxSInt : SignedIntOpTypes() {
        override fun toString(): String {
            return "max_sint"
        }

        val patterns = listOf(
            SmtPatterns.maxInt
        )
    }
}

/**
 * Collection of some patterns that we use in this file for matching.
 */
object SmtPatterns {
    val script = FactorySmtScript

    val maxInt = script.number(MAX_EVM_INT256)

    /**
    or(
    isNegativeSignedInt(lhs) and isPositiveSignedInt(rhs),
    areOfSameSign(lhs, rhs) and (lhs intLe rhs)
    )
     */
    val sLePattern = script {
        val lhs = SmtExp.PlaceHolder("lhs", Sort.IntSort)
        val rhs = SmtExp.PlaceHolder("rhs", Sort.IntSort)
        or(
            and(
                isNegativeSignedIntPattern(lhs),
                isPositiveSignedIntPattern(rhs),
            ),
            and(
                areOfSameSign(lhs, rhs),
                lhs le rhs,
            ),
        )
    }

    /**
    isPositiveSignedInt(e: LExpression) = lxf { e intLe NUM(MAX_EVM_INT256) }
     */
    fun isPositiveSignedIntPattern(e: SmtExp) = script { e le maxInt }

    /**
    isNegativeSignedInt(e: LExpression) = lxf { e intGt NUM(MAX_EVM_INT256) }
     */
    fun isNegativeSignedIntPattern(e: SmtExp) = script { e gt maxInt }

    /**
    areOfSameSign(e1: LExpression, e2: LExpression) = lxf { isPositiveSignedInt(e1) eq isPositiveSignedInt(e2) }
     */
    fun areOfSameSign(e1: SmtExp, e2: SmtExp) =
        script { isPositiveSignedIntPattern(e1) eq isPositiveSignedIntPattern(e2) }
}
