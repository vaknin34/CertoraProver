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

package analysis.numeric.linear

import com.certora.collect.*
import datastructures.stdcollections.*
import utils.*
import vc.data.TACExpr
import vc.data.TACSymbol
import vc.data.tacexprutil.TACExprFreeVarsCollector
import java.math.BigInteger

typealias LinearInvariants = TreapSet<LinearEquality>

/**
 * Join two sets of invariants without canonicalizing first
 */
fun LinearInvariants.fastJoin(other: LinearInvariants) = this.intersect(other)

/**
 * Join two sets after canonicalizing each
 */
fun LinearInvariants.join(other: LinearInvariants) = this.mapToTreapSet { it.canonicalize() }.fastJoin(
        other.mapToTreapSet(LinearEquality::canonicalize)
)

/**
 * Remove all invariants relating [lhs]
 */
fun LinearInvariants.kill(lhs: TACSymbol.Var) = this.removeAll { it.relates(lhs) }

fun LinearInvariants.killAll(lhs: TreapSet<TACSymbol.Var>) = this.removeAll {
    it.relatesAny(lhs)
}

fun LinearInvariants.termEquality(v: List<Pair<LVar, BigInteger>>, other: List<Pair<LVar, BigInteger>>) : Boolean {
    if(v.map { it.first }.toSet().containsAny(other.map { it.first })) {
        // XXX(jtoman): should probably just throw
        return false
    }
    val m1  = v.map { it.first to it.second.negate() }.toMap() + other.toMap()
    val m2 = v.toMap() + other.map { it.first to it.second.negate() }.toMap()
    return this.any { p ->
        p.k == BigInteger.ZERO &&
                (m1 == p.term || m2 == p.term)
    }
}

@Suppress("unused")
fun LinearInvariants.termEquality(v: Pair<LVar, BigInteger>, other: List<Pair<LVar, BigInteger>>) = termEquality(other, v)

fun LinearInvariants.termEquality(v: List<Pair<LVar, BigInteger>>, other: Pair<LVar, BigInteger>) = termEquality(v, listOf(other))

@Suppress("unused")
fun LinearInvariants.termEquality(p1: Pair<LVar, BigInteger>, p2: Pair<LVar, BigInteger>): Boolean =
        termEquality(listOf(p1), listOf(p2))

/**
 * Checks if the set of equalities imply the given linear equality. This check is *very* basic, and just
 * checks set membership (modulo canonicalization)
 */
infix fun LinearInvariants.implies(l: LinearEquality) : Boolean {
    val canonLE = l.canonicalize()
    // this is a tautology, like `x = x`
    if(canonLE.term.isEmpty() && canonLE.k == BigInteger.ZERO) {
        return true
    }
    return this.any {
        it.canonicalize() == canonLE
    }
}

/**
 * Checks if the set of equalities imply the linear equality returned from the builder. Currently is
 * a very simple membership check.
 */
infix fun LinearInvariants.implies(f: LinearEquality.Builder.() -> LinearEquality) : Boolean {
    return this implies LinearEquality.build {
        this.f()
    }
}

/** Checks if the set of canonical equalities imply the given linear equality */
infix fun LinearInvariants.alreadyCanonImplies(l: LinearEquality) : Boolean {
    return l.canonicalize() in this
}

/** Checks if the set of canonical equalities imply the linear equality returned from the builder */
infix fun LinearInvariants.alreadyCanonImplies(f: LinearEquality.Builder.() -> LinearEquality) : Boolean {
    return this alreadyCanonImplies LinearEquality.build {
        this.f()
    }
}


/**
 * For an assignment of [rhs] to the variable [lhs], what new sets of linear equalities can be derived?
 */
fun LinearInvariants.genFor(lhs: TACSymbol.Var, rhs: TACExpr) = TACExprFreeVarsCollector.getFreeVars(rhs).let { fv ->
    this.parallelMapReduce(
        map = { runIf(it.canGenFor(fv, lhs)) { it.gen(lhs, rhs) }.orEmpty() },
        reduce = { l, r -> l + r }
    ).orEmpty()
}

fun LinearInvariants.substitute(concr: TACSymbol.Var, sym: LVar.Instrumentation): LinearInvariants = this.mutate { toRet ->
    for(l in this) {
        toRet.add(l)
        if(!l.relates(sym) || l.relates(concr)) {
            continue
        }
        toRet.add(l.substSynthetic(concr, sym))
    }
}

fun LinearInvariants.canonicalize() : LinearInvariants = this.updateElements { it.canonicalize() }

fun LinearInvariants.propagateConstant(subst: (TACSymbol.Var) -> BigInteger?) : LinearInvariants = this.mutate { toRet ->
    for(l in this) {
        val toMap = l.term.keys.filterIsInstance(LVar.PVar::class.java).mapNotNull { pv ->
            subst(pv.v)?.let { pv to it }
        }.toMap()
        if(toMap.isNotEmpty()) {
            l.withConst(toMap).let(toRet::add)
        }
    }
}

fun LinearInvariants.propagateEquality(eqs: List<Pair<TACSymbol.Var, TACSymbol.Var>>, valuation: (TACSymbol.Var) -> BigInteger?) : LinearInvariants {
    return propagateEqualities(listOf(), eqs, valuation)
}

fun LinearInvariants.propagateEqualities(scaledEq: List<Pair<TACSymbol.Var, Pair<TACSymbol.Var, BigInteger>>>, eqs: List<Pair<TACSymbol.Var, TACSymbol.Var>>, valuation: (TACSymbol.Var) -> BigInteger?) : LinearInvariants = mutate { toRet ->
    for(l in this) {
        for((v1, v2) in eqs) {
            toRet.addAll(l.genEquality(v1, v2))
        }
        for((v1, vKPair) in scaledEq) {
            toRet.addAll(l.genEquality(v1, vKPair))
        }
    }
}.propagateConstant(valuation)
