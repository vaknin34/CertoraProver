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

import algorithms.EquivalenceRelation
import smtlibutils.algorithms.CollectQualIds.Companion.collectQualIds
import smtlibutils.data.SmtExp

/**
 * Simple implementation of E-Matching.
 *
 * E-matching is like pattern matching, but in addition takes into account a set of equalities.
 *
 * E.g. if the set of equalities is { a = f(g(b)) }
 *  then the pattern `f(g(x))` matches the term `a` with the substitution [x -> b].
 */
class EMatching(val eGraph: MutableCongruenceClosure) {

    private val debugMode = true

    /**
     * @param variables the [SmtExp.QualIdentifier]s in [pattern] that are to be interpreted as variables (the others
     *      are interpreted as constants).
     */
    fun match(pattern: SmtExp, variables: Set<SmtExp.QualIdentifier>, toMatch: SmtExp): Set<SmtExpSubstitution> =
        match(pattern, variables, toMatch, emptySet()) ?: setOf()

    private fun match(
        pattern: SmtExp,
        variables: Set<SmtExp.QualIdentifier>,
        toMatch: SmtExp,
        substitutions: Set<SmtExpSubstitution>
    ): Set<SmtExpSubstitution>? {
        if (pattern.sort != toMatch.sort)
            return null
        val res = when (pattern) {
            is SmtExp.Apply -> matchApp(pattern, variables, toMatch, substitutions)
            is SmtExp.QualIdentifier ->
                if (pattern in variables)
                    matchVar(pattern, variables, toMatch, substitutions)
                else
                    matchConst(pattern, toMatch, substitutions)
            is SmtExp.BitvectorLiteral, is SmtExp.BoolLiteral, is SmtExp.IntLiteral ->
                matchConst(pattern, toMatch, substitutions)
            else -> error("expression not allowed in E-matching")
        }
        check(!debugMode || matchContract(pattern, toMatch, res, eGraph, variables))
        return res
    }

    private fun matchApp(
        pattern: SmtExp.Apply,
        variables: Set<SmtExp.QualIdentifier>,
        toMatch: SmtExp,
        substitutions: Set<SmtExpSubstitution>
    ): Set<SmtExpSubstitution>? {
        val equivalentAndMatchingApps =
//            eGraph.getEquivalentFunctionApplications(toMatch, pattern.fs)
            eGraph.getEquivalenceClass(toMatch)
                .filter { it.sort == pattern.sort &&  it is SmtExp.Apply && it.fs == pattern.fs && it.args.size == pattern.args.size && it.args.zip(pattern.args).all { (l, r) -> l.sort == r.sort } }
                .filterIsInstance<SmtExp.Apply>()
        if (equivalentAndMatchingApps.isEmpty()) return null
        var res: MutableSet<SmtExpSubstitution>? = null
        equivalentAndMatchingApps.forEach outer@{ eqApp ->
            val argToSubss = if (debugMode) mutableListOf<Set<SmtExpSubstitution>>() else null
            var res1 = substitutions
            eqApp.args.forEachIndexed { i, ti ->
                res1 = match(pattern.args[i], variables, ti, res1) ?: return@outer
                argToSubss?.add(res1)
            }
            if (res == null)
                res = mutableSetOf()
            res!!.addAll(res1)
            check(!debugMode || matchContract(pattern, eqApp, res1, eGraph, variables))
            check(!debugMode || matchContract(pattern, toMatch, res1, eGraph, variables))
        }
        check(!debugMode || matchContract(pattern, toMatch, res, eGraph, variables))
        return res
    }

    private fun matchVar(
        x: SmtExp.QualIdentifier,
        variables: Set<SmtExp.QualIdentifier>,
        toMatch: SmtExp,
        substitutions: Set<SmtExpSubstitution>
    ): Set<SmtExpSubstitution>? {
        if (substitutions.isEmpty()) {
            val res = setOf(SmtExpSubstitution.Empty.appendParallel(x, eGraph.getRepresentative(toMatch)))
            check(!debugMode || matchVarContract(x, toMatch, res, eGraph, substitutions, variables))
            return res
        }

        val res = mutableSetOf<SmtExpSubstitution>()
//        substitutions
//            .filter { x !in it.domain() }
//            .forEach { res.add(it.appendParallel(x, eGraph.getRepresentative(toMatch))) }
//        substitutions
//            .filter { eGraph.areEqual(it.applyTo(x), toMatch) }
//            .forEach { res.add(it) }

        substitutions.forEach {
            if (x in it.domain()) {
                if (eGraph.areEqual(it.applyTo(x), toMatch))
                    res.add(it)
            } else {
                res.add(it.appendParallel(x, eGraph.getRepresentative(toMatch)))
            }
        }


//        check(!debugMode || matchContract(x, toMatch, res, eGraph))
        check(!debugMode || matchVarContract(x, toMatch, res, eGraph, substitutions, variables))

        if (res.isEmpty()) {
            // all the incoming substitutions (non-empty in this branch) are incompatible -- can't match, return null
            check(!debugMode || substitutions.all { subs -> x in subs.domain() && !eGraph.areEqual(toMatch, subs.applyTo(x)) })
            return null
        }

        return res
    }


    private fun matchConst(
        c: SmtExp,
        toMatch: SmtExp,
        substitutions: Set<SmtExpSubstitution>
    ): Set<SmtExpSubstitution>? =
        if (eGraph.areEqual(c, toMatch))
            substitutions
        else
            null


    companion object {

        /**
         * This should hold for the input-output triple of [match].
         */
        fun matchContract(
            pattern: SmtExp,
            toMatch: SmtExp,
            matchRes: Set<SmtExpSubstitution>?,
            eGraph: EquivalenceRelation<SmtExp>,
            variables: Set<SmtExp.QualIdentifier>
        ): Boolean {
            if (matchRes == null) return true
            matchRes.forEach { subs ->
                /* substitution must make the pattern equal to the match target */
                if (!eGraph.areEqual(subs.applyTo(pattern), toMatch))
                    return false
                /* substitution must be complete with respect to the variables in the pattern,
                * (it might contain more, due to substitutions coming from "neighboring argument expressions"
                * due to the matching algorithm */
                if (!subs.domain().containsAll(collectQualIds(pattern).filter { it in variables  }))
                    return false
            }
            return true
        }


        private fun matchVarContract(
            x: SmtExp.QualIdentifier,
            toMatch: SmtExp,
            res: Set<SmtExpSubstitution>,
            eGraph: MutableCongruenceClosure,
            oldSubstitutions: Set<SmtExpSubstitution>,
            variables: Set<SmtExp.QualIdentifier>
        ): Boolean {
            /* the new substitutions must be compatible with the old ones */
            res.forEach { newSubs ->
                if (newSubs.domain() == setOf(x) && oldSubstitutions.isEmpty())
                    return@forEach

                val newSubsDomainMinusX = newSubs.domain() - x

                var predecessorSubs: SmtExpSubstitution? = null
                oldSubstitutions.forEach { oldSubs ->
                    if (oldSubs.domain() == newSubsDomainMinusX || oldSubs == newSubs) {
//                        check(predecessorSubs == null) { "having two predecessors -- shouldn't happen, right?"} // EDIt: can happen if one is a subset
                        predecessorSubs = oldSubs
                    }
                }
                if (predecessorSubs == null)
                    return false
            }

            /* also, check the standard contract for match...(..) functions */
            if (!matchContract(x, toMatch, res, eGraph, variables)) return false
            return true
        }

    }

}