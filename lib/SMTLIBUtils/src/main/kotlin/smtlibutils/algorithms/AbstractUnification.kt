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

package smtlibutils.algorithms

import utils.`impossible!`
import utils.uncheckedAs

/**
 * Represents S-Expressions.
 * We can annotate this interface and the subinterfaces appropriately whenever we have an s-expression like structure
 * and we want to apply the unification infrastructure.
 *
 * [EXP] : the base class of the expressions we're dealing with, e.g. SmtExp, or Sort
 * [FS] : the class of the "function symbols" of [EXP], SmtFunctionSymbol for SmtExp, SortSymbol for Sort
 */
interface SExp<EXP: SExp<EXP, FS>, FS>

interface SExpApply<EXP: SExp<EXP, FS>, FS> : SExp<EXP, FS> {
    val fs: FS
    val args: List<EXP>
}

interface SExpSym<EXP: SExp<EXP, FS>, FS> : SExp<EXP, FS>

interface SExpVar<EXP: SExp<EXP, FS>, FS> : SExp<EXP, FS>


/**
 * Implementation of the standard algorithm to compute the most general unifier of two [SExp]s.
 *
 * A unifier of two [SExp]r `s`, `t` is a substitution sigma that, applied to both expressions, makes them the same,
 * i.e., `sigma(s) = sigma(t)`.
 *
 * The most general unifier is, intuitively the unifier that leaves `sigma(s)` as the most-general possible expression,
 *  i.e., `f(x)` is preferred over `f(f(x))` and `f(13)` (assuming `x` is an [SExpVar] and `13` is an [SExpSym]).
 * Formally, I guess this means that we maximize the cardinality of the set of possible instantiations of `sigma(s)`,
 * i.e. { theta(sigma(x)) | theta is a substitution }.
 *
 * Implementation inspired by [https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf]
 *
 * @param applyExp function that builds a term by applying a [FS] to a list of [EXP]s
 * @param auxTupleConstr given an arity constructs [FS] that is different from all other [FS]s that appear (used to
 *    construct an auxiliary tuple of terms -- this makes it easy handle the case where we want to unify two tuples)
 * @param EXP the s-expression type
 * @param FS the function symbol type
 */
abstract class AbstractUnification<EXP : SExp<EXP, FS>, FS>(
    val applyExp: (FS, List<EXP>) -> EXP,
    val auxTupleConstr: (Int) -> FS,
) {

    fun unify(s: EXP, t: EXP): SExp<EXP, FS>? =
        computeUnifier(s, t)?.applyTo(s)

    fun unifySorts(rank: List<EXP>, instantiatedParamSorts: List<EXP>): List<EXP> =
            (computeUnifier(rank.dropLast(1), instantiatedParamSorts)?.applyTo(rank)
            ?: error("Sort error; failed to unify parameter sorts ${rank.dropLast(1)} and $instantiatedParamSorts"))

    fun unifySort(rank: List<EXP>, instantiatedResultSort: EXP): List<EXP> =
        (computeUnifier(rank.last(), instantiatedResultSort)?.applyTo(rank)
            ?: error("Sort error; failed to unify result sort ${rank.last()} and $instantiatedResultSort"))


    fun computeUnifier(s: EXP, t: EXP) =
        unify(s, t, Substitution(applyExp))

    /**
     * Compute the unifier for two lists [s] and [t] of sorts.
     * This unifier is defined as the unifier of the two sorts constructed by applying an auxiliary function symbol
     * (called "Tuple") to both lists, i.e., we compute the result of unify((Tuple [s]), (Tuple [t])).
     */
    fun computeUnifier(s: List<EXP>, t: List<EXP>): Substitution<EXP, FS>? {
        if (s.size != t.size) return null
        val tupleAuxSymbol = auxTupleConstr(s.size)
        val sTuple = applyExp(tupleAuxSymbol, s)
        val tTuple = applyExp(tupleAuxSymbol, t)
        return computeUnifier(sTuple, tTuple)
    }

    fun isApp(s: SExp<EXP, FS>): Boolean = s is SExpApply<EXP, FS>
    fun isVar(s: SExp<EXP, FS>): Boolean = s is SExpVar<EXP, FS>
    fun isSym(s: SExp<EXP, FS>): Boolean = s is SExpSym<EXP, FS>

    /**
     * @return most general unified expression from [s_in] and [t_in], null if there is none
     */
    private fun unify(
        s_in: EXP,
        t_in: EXP,
        sigma: Substitution<EXP, FS>
    ): Substitution<EXP, FS>? {
        var s = s_in
        var t = t_in
        if (isVar(s)) {
            s = sigma.applyTo(s)
        }
        if (isVar(t)) {
            t = sigma.applyTo(t)
        }
        return if (isVar(s) && s == t) {
            sigma
        } else if (isSym(s) && isSym(t)) {
            if (s == t) sigma else null
        } else if (isApp(s) && isSym(t)) {
            null
        } else if (isSym(s) && isApp(t)) {
            null
        } else if (isApp(s) && isApp(t)) {
            val sApp = s.uncheckedAs<SExpApply<EXP, FS>>()
            val tApp = t.uncheckedAs<SExpApply<EXP, FS>>()
            if (sApp.fs == tApp.fs) {
                var sigmaUp: Substitution<EXP, FS>? = sigma
                sApp.args.zip(tApp.args).forEach { (sArg, tArg) ->
                    if (sigmaUp == null) return null
                    sigmaUp = unify(sArg, tArg, sigmaUp!!)
                }
                sigmaUp
            } else {
                null
            }
        } else if (!isVar(s)) {
            unify(t, s, sigma)
        } else if (occursIn(s.uncheckedAs<SExpVar<EXP, FS>>(), t)) {
            null
        } else {
            val compose =
                Substitution.compose(sigma, Substitution(s.uncheckedAs<SExpVar<EXP, FS>>() to t, applyExp))
            if (compose == null) {
                null
            } else {
                unify(s, t, compose)
            }
        }
    }


    private fun occursIn(s: SExpVar<EXP, FS>, t: SExp<EXP, FS>): Boolean = when {
        isSym(t) -> false
        isVar(t) -> s == t
        isApp(t) -> (t as SExpApply).args.any { occursIn(s, it) }
        else -> `impossible!`
    }

    /**
     * This represents a somewhat restricted notion of substitution as a sequential composition of single-pair
     * substitutions (hence the restricted public constructors).
     *
     * We use it to represent the result of a unification (i.e. the most general unifier).
     */
    class Substitution<EXP : SExp<EXP, FS>, FS> private constructor(
        val pairs: List<Pair<SExpVar<EXP, FS>, EXP>>,
        val applyExp: (FS, List<EXP>) -> EXP,
    ) {
        constructor(
            pair: Pair<SExpVar<EXP, FS>, EXP>,
            applyExp: (FS, List<EXP>) -> EXP,
        ) : this(listOf(pair), applyExp)

        constructor(
            applyExp: (FS, List<EXP>) -> EXP,
        ) : this(listOf(), applyExp)

        companion object {
            private fun <EXP : SExp<EXP, FS>, FS> substitute(
                vrble: SExpVar<EXP, FS>,
                sub: Substitution<EXP, FS>
            ): EXP {
                var res = vrble.uncheckedAs<EXP>()
                sub.pairs.forEach { (v, e) ->
                    if (res == v) {
                        res = e
                    }
                }
                return res
            }

            fun <EXP : SExp<EXP, FS>, FS> compose(
                l: Substitution<EXP, FS>?,
                r: Substitution<EXP, FS>?
            ): Substitution<EXP, FS>? =
                if (l == null || r == null) {
                    null
                } else {
                    check(l.applyExp == r.applyExp) { "this shouldn't happen ($l ; $r)" }
                    Substitution(
                        pairs = l.pairs + r.pairs,
                        applyExp = l.applyExp
                    )
                }
        }

        override fun toString(): String = pairs.toString()

        fun applyTo(rank: List<EXP>): List<EXP> =
            rank.map(::applyTo)

        fun applyTo(term: EXP): EXP = when (term) {
            is SExpSym<*, *> -> term
            is SExpVar<*, *> -> substitute(term.uncheckedAs<SExpVar<EXP, FS>>(), this)
            is SExpApply<*, *> -> applyExp(term.fs.uncheckedAs<FS>(), term.args.map { applyTo(it.uncheckedAs<EXP>()) })
            else -> `impossible!`
        }
    }
}