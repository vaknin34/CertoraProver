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
import evm.EVM_BITWIDTH256
import utils.*
import vc.data.TACExpr
import vc.data.TACSymbol
import vc.data.asTACSymbol
import vc.data.tacexprutil.TACExprFreeVarsCollector
import java.math.BigInteger
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract

/**
 * A linear equality, represented by a (non-empty) sequence of ri * vi (encoded in [term]) and a number [k].
 *
 * If a [LinearEquality] holds, then we must have that r1 * v1 + r2 * v2 + ... + rn * v2 + k == 0.
 */
data class LinearEquality(val term: TreapMap<LVar, BigInteger>, val k: BigInteger) {
    // Cache the set of variables in this equality for quick set intersections
    val pvars: TreapSet<TACSymbol.Var> = term.keys.mapNotNullToTreapSet { (it as? LVar.PVar)?.v }

    /**
     * Does this relate the variable [v]
     */
    fun relates(v: TACSymbol.Var): Boolean = v in pvars

    /**
     * does this relate any of the variables in [vs]
     */
    fun relatesAny(vs: TreapSet<TACSymbol.Var>) : Boolean = vs.containsAny(pvars)

    /*
     * if we have [v] + a0 * x0 + a1 * x1 + ... + k == 0
     *   return ([x0 |-> -a0, x1 |-> -a1, ...], -k), i.e. the representation of
     *     a summation of terms equivalent to [v]
     */
    fun definingCoeffAndOffsetFor(v: TACSymbol.Var): Pair<Map<LVar, BigInteger>, BigInteger>? {
        if (!relates(v)) {
            return null
        }

        val f = term[LVar.PVar(v)]?.let { k ->
            k.negate().takeIf {
                it.abs() == BigInteger.ONE
            }
        } ?: return null

        val ts = term.mapValuesNotNull {(lv, k) ->
            (f*k).takeIf {
                lv !is LVar.PVar || lv.v != v
            }
        }

        val off = f*k

        return ts to off
    }

    /**
     * takes [term] and [k] of a [LinearEquality] and reduces using gcd of the coefficients of [term] and [k]
    * */
    private fun reduce (eqs: TreapMap<LVar, BigInteger>, k: BigInteger) : Pair<TreapMap<LVar, BigInteger>, BigInteger> {
        val gcd = eqs.values.reduce(BigInteger::gcd).gcd(k)
        if(gcd == BigInteger.ONE || gcd == BigInteger.ZERO) {
            return eqs to k
        }
        return eqs.updateValues { _, v -> v / gcd } to k / gcd
    }


    /**
     * Assuming this [LinearEquality] holds, what equalities hold after *assigning* [newVar] := [e].
     *
     * It is assumed that FV(e) /\ dom([term]) is not empty
     */
    fun gen(newVar: TACSymbol.Var, e: TACExpr): TreapSet<LinearEquality> {
        check(this.relatesAny(TACExprFreeVarsCollector.getFreeVars(e)))
        return when (e) {
            is TACExpr.BinExp -> {
                val o1 = e.o1AsNullableTACSymbol()
                val o2 = e.o2AsNullableTACSymbol()
                if (o1 == null || o2 == null) {
                    treapSetOf()
                } else {
                    when (e) {
                        is TACExpr.BinOp.ShiftLeft -> {
                            if(o2 !is TACSymbol.Const || o2.value >= EVM_BITWIDTH256.toBigInteger()) {
                                treapSetOf()
                            } else {
                                gen(
                                    newVar, TACExpr.Vec.Mul(
                                        o1.asSym(), BigInteger.TWO.pow(o2.value.toInt()).asTACSymbol().asSym()
                                    )
                                )
                            }
                        }
                        is TACExpr.Vec.Add -> {
                            val toRet = treapSetBuilderOf<LinearEquality>()
                            if (validSubstitutionTarget(newVar, o1, o2)) {
                                /* we can invert newLhs = o1 + o2 to o1 = newLhs - o2 (assuming o2 != newLhs) */
                                toRet.add(
                                    subst(o1, newVar to BigInteger.ONE, o2 to BigInteger.ONE.negate())
                                )
                            }
                            if (validSubstitutionTarget(newVar, o2, o1)) {
                                /*
                                    We can invert newLhs = o1 + o2 to o2 = newLhs - o1 (assuming o1 != newLhs)
                                     */
                                toRet.add(
                                    subst(o2, newVar to BigInteger.ONE, o1 to BigInteger.ONE.negate())
                                )
                            }
                            toRet.build()
                        }
                        is TACExpr.Vec.Mul -> {
                            val toRet = treapSetBuilderOf<LinearEquality>()
                            /* We cannot invert non-linear multiplication */
                            if (o1 is TACSymbol.Var && o2 is TACSymbol.Var) {
                                listOf<LinearEquality>()
                            } else if (validSubstitutionTarget(newVar, o1) && o2 is TACSymbol.Const) {
                                val mut = treapMapBuilderOf<LVar, BigInteger>()
                                /* To invert newVar = o1 * o2, we have o1 = newVar / o2 */
                                assert(LVar.PVar(o1) in term)
                                /* directly update all coefficients in term and also k.
                                         This means say we had a * o1 + b * y + c * z + k = 0,
                                         then after this update we will have:
                                         a * newVar + b * o2 * y + c * o2 * z + k * o2 = 0. */
                                mut[LVar.PVar(newVar)] = term[LVar.PVar(o1)]!!
                                // go over the rest of the terms in term and change their coefficients
                                val keys = term.keys
                                for (vr in keys) {
                                    if ((vr as? LVar.PVar)?.v != o1) {
                                        mut[vr] = term[vr]!! * o2.value
                                    }
                                }
                                // update k
                                val k_ = k * o2.value
                                // reduce k and all coefficients
                                val (terms, k) = reduce(mut.build(), k_)
                                toRet.add(LinearEquality(terms, k))
                            } else if (validSubstitutionTarget(newVar, o2) && o1 is TACSymbol.Const) {
                                val mut = treapMapBuilderOf<LVar, BigInteger>()
                                /* Symmetrically */
                                assert(LVar.PVar(o2) in term)
                                mut[LVar.PVar(newVar)] = term[LVar.PVar(o2)]!!
                                val keys = term.keys
                                for (vr in keys) {
                                    if ((vr as? LVar.PVar)?.v != o2) {
                                        mut[vr] = term[vr]!! * o1.value
                                    }
                                }
                                // update k
                                val k_ = k * o1.value
                                // reduce k and all coefficients
                                val (terms, k) = reduce(mut.build(), k_)
                                toRet.add(LinearEquality(terms, k))
                            }
                            toRet.build()
                        }
                        is TACExpr.BinOp.Sub -> {
                            val toRet = treapSetBuilderOf<LinearEquality>()
                            if (validSubstitutionTarget(newVar, o1, o2)) {
                                /*
                                   we can invert newLhs = o1 - o2 by
                                   o1 = newLhs + o2
                                */
                                toRet.add(
                                    subst(o1, newVar to BigInteger.ONE, o2 to BigInteger.ONE)
                                )
                            }
                            if (validSubstitutionTarget(newVar, o2, o1)) {
                                term[LVar.PVar(o2)] ?: error("could not find o2=$o2 in term $term")
                                /*
                                    We can invert newLhs = o1 - o2 by
                                    o2 = o1 - newLhs (note scale.neg() below)
                                     */
                                toRet.add(
                                    subst(o2, newVar to BigInteger.ONE.negate(), o1 to BigInteger.ONE)
                                )
                            }
                            toRet.build()
                        }
                        else -> treapSetOf()
                    }
                }
            }
            is TACExpr.Sym -> {
                if (!validSubstitutionTarget(newVar, e.s)) {
                    treapSetOf()
                } else {
                    val x = LVar.PVar(e.s as TACSymbol.Var)
                    assert(x in term)
                    val scale = term[x]!!
                    treapSetOf(
                        copy(term = term.minus(x) + (LVar.PVar(newVar) to scale))
                    )
                }
            }
            else -> treapSetOf()
        }
    }

    @Suppress("unused")
    interface Builder {
        val `1` : BigInteger
        val `0` : BigInteger
        val `-1` : BigInteger

        /**
         * DSL Operation: build a [LinearEquality] that represents the equality between the two [LinearTerm]s
         */
        infix fun LinearTerm.`=`(other: LinearTerm) : LinearEquality {
            val toRet = treapMapBuilderOf<LVar, BigInteger>()
            for((k, v) in this.terms) {
                toRet[k] = v + (toRet[k] ?: `0`)
            }
            return other.terms.fold(toRet) { Curr, (k,v) ->
                if(k in Curr) {
                    Curr[k] = (Curr[k]!! + v.negate())
                } else {
                    Curr[k] = v.negate()
                }
                Curr
            }.let { t ->
                LinearEquality(term = t.build(), k = this.k - other.k)
            }
        }

        infix fun LVar.`=`(other: LVar) : LinearEquality = this * `1` `=` other * BigInteger.ONE
        infix fun LVar.`=`(other: LinearAtom) = this * `1` `=` other
        infix fun LVar.`=`(other: LinearTerm) = this * `1` `=` other

        infix fun List<LinearAtom>.`=`(other: List<LinearAtom>) = LinearTerm(this) `=` LinearTerm(other)

        infix fun LinearAtom.`=`(other: LinearAtom) : LinearEquality = listOf(this) `=` listOf(other)
        infix fun LinearAtom.`=`(other: LinearTerm) : LinearEquality = LinearTerm(listOf(this)) `=` other
        infix fun LinearAtom.`=`(other: LVar) = this `=` other * `1`


        infix fun LinearTerm.`=`(other: LinearAtom) : LinearEquality = this `=` LinearTerm(listOf(other))
        infix fun LinearTerm.`=`(other: LVar) : LinearEquality = this `=` other * `1`

        operator fun TACSymbol.Var.not() = this.lift()
        operator fun TACSymbol.not() = when(this) {
            is TACSymbol.Const -> LinearTerm(k = this.value, terms = listOf())
            is TACSymbol.Var ->  LinearTerm(listOf(LVar.PVar(this) to BigInteger.ONE), k = BigInteger.ZERO)
        }

        fun TACSymbol.Var.lift() = LVar.PVar(this)

        fun BigInteger.lift() = LinearTerm(
            k = this,
            terms = listOf()
        )

        fun Int.lift() = this.toBigInteger().lift()
    }

    companion object {
        inline fun <R> build(crossinline f: Builder.() -> R) : R {
            return (object : Builder {
                override val `1` = BigInteger.ONE
                override val `0` = BigInteger.ZERO
                override val `-1` = BigInteger.ONE.negate()
            }).f()
        }
    }

    fun genEquality(v1: TACSymbol.Var, v2: TACSymbol.Var) : List<LinearEquality> {
        if(!this.relates(v1) && !this.relates(v2)) {
            return listOf()
        }
        if(v1 == v2) {
            return listOf()
        }
        val toReturn = mutableListOf<LinearEquality>()
        if(this.relates(v1)) {
            substituteEq(v1, v2, BigInteger.ONE, toReturn)
        }
        if(this.relates(v2)) {
            substituteEq(v2, v1, BigInteger.ONE, toReturn)
        }
        if(this.relates(v1) && this.relates(v2)) {
            val termMap = this.term.builder()
            val tmpC = termMap[LVar.PVar(v1)]!!
            termMap[LVar.PVar(v1)] = termMap[LVar.PVar(v2)]!!
            termMap[LVar.PVar(v2)] = tmpC
            toReturn.add(LinearEquality(termMap.build(), k))
        }
        return toReturn
    }


    /**
     * Propagate that [v1] is equal to [other].first * [other].second
     */
    fun genEquality(v1: TACSymbol.Var, other: Pair<TACSymbol.Var, BigInteger>) : List<LinearEquality> {
        val v2 = other.first
        if(!this.relates(v1) && !this.relates(v2)) {
            return listOf()
        }
        val toReturn = mutableListOf<LinearEquality>()
        if(this.relates(v1)) {
            substituteEq(v1, v2, other.second, toReturn)
        }
        /**
         * if we have ... v1 * k + v2 * j ... and [other].second divides j, then by v1 = v2 * [other].second we have:
         * ... v2 * k * [other].second + v1 * j / [other].second ...
         */
        if(this.relates(v1) && this.relates(v2)) {
            val termMap = this.term.builder()
            val tmpC = termMap[LVar.PVar(v1)]!!
            if(tmpC.mod(other.second) == BigInteger.ZERO) {
                termMap[LVar.PVar(v1)] = termMap[LVar.PVar(v2)]!! / other.second
                termMap[LVar.PVar(v2)] = tmpC * other.second
                toReturn.add(LinearEquality(termMap.build(), k))
            }
        }
        return toReturn
    }

    /**
     * Within this term (which must relate [v1]), substitute that [v2] * [factor] is equal to [v1], placing the result in [toReturn].
     *
     * If this term also relates [v2] then the factors of [v1] and [v2] are combined to be the new factor for [v2],
     * otherwise, [v2] is simply substituted for [v1].
     *
     * Examples:
     * `x * 5 = y [z*4/x] => z * 20 = y`
     * `x * 5 + z * 2 = y [z*4/x] => z * 22 = y`
     * `x * 5 - z * 10 = y [z*2/x] => y = 0`
     */
    private fun substituteEq(v1: TACSymbol.Var, v2: TACSymbol.Var, factor: BigInteger, toReturn: MutableList<LinearEquality>) {
        require(v1 != v2)
        val c1 = this.term[LVar.PVar(v1)]!!
        val c2 = (this.term[LVar.PVar(v2)] ?: BigInteger.ZERO) + c1 * factor
        val termMap = this.term.builder()
        termMap.remove(LVar.PVar(v1))
        if (c2 == BigInteger.ZERO) {
            termMap.remove(LVar.PVar(v2))
        } else {
            termMap[LVar.PVar(v2)] = c2
        }
        toReturn.add(LinearEquality(
                termMap.build(), k
        ).canonicalize())
    }

    private val comp = Comparator.comparing { it: LVar ->
        if (it is LVar.Instrumentation) {
            0
        } else {
            1
        }
    }.thenComparingInt { it ->
        it.hashCode()
    }.thenComparing {
        o: LVar -> o.toString()
    }

    private lateinit var canon : LinearEquality

    private fun unsafeMarkCanonical() : LinearEquality {
        canon = this
        return this
    }

    /**
     * Canonicalize this linear equality.
     */
    fun canonicalize() : LinearEquality {
        if(this::canon.isInitialized) {
            return canon
        }
        var currHead : LVar? = null
        var gcd = this.k.abs()
        val toRet = this.term.updateValues { key, value ->
            if(value != BigInteger.ZERO) {
                if(currHead == null || comp.compare(key, currHead) < 0) {
                    currHead = key
                }
                gcd = value.gcd(gcd)
                value
            } else {
                null
            }
        }.builder()
        var k = this.k
        if(toRet.isEmpty()) {
            return LinearEquality(term = treapMapOf(), k = k)
        }
        check(currHead != null)
        val st = currHead
        val doNegate = toRet[st]!! < BigInteger.ZERO
        check(gcd >= BigInteger.ZERO)
        val doReduce = gcd > BigInteger.ONE
        if(doNegate || doReduce) {
            k = (if(doNegate) k.negate() else k)
            if(doReduce) {
                k /= gcd
            }
            val it = toRet.iterator()
            while(it.hasNext()) {
                val ent = it.next()
                var value = ent.value
                if(doNegate) {
                    value = value.negate()
                }
                if(doReduce) {
                    value /= gcd
                }
                ent.setValue(value)
            }
        }
        canon = LinearEquality(term = toRet.build(), k = k).unsafeMarkCanonical()
        return canon
    }

    fun updateSynthetic(synth: LVar.Instrumentation, const: BigInteger): LinearEquality {
        if(!this.relates(synth)) {
            return this
        }
        val scale = this.term[synth]!!
        return this.copy(
                k = k + scale.negate() * const
        )
    }

    fun updateSynthetic(synth: LVar.Instrumentation, other: LVar.PVar, otherScale: BigInteger) : LinearEquality {
        if(!this.relates(synth)) {
            return this
        }
        val scale = this.term[synth]!!
        return if(other in this.term) {
            this.copy(
                term = term + (other to this.term[other]!! - (scale * otherScale))
            )
        } else {
            this.copy(
                term = term + (other to (scale * otherScale).negate())
            )
        }
    }

    fun updateSynthetic(synth: LVar.Instrumentation, other: LVar.PVar) : LinearEquality {
        return updateSynthetic(synth, other, BigInteger.ONE)
    }

    private fun subst(o1: TACSymbol.Var, pair: Pair<TACSymbol.Var, BigInteger>, vararg comb: Pair<TACSymbol, BigInteger>) : LinearEquality {
        val mut = term.builder()
        val currScale = mut[LVar.PVar(o1)]!!
        mut.remove(LVar.PVar(o1))
        val substKey = LVar.PVar(pair.first)
        val touched = mutableSetOf(substKey)
        mut[substKey] = pair.second * currScale
        var k_ = this.k

        for ((s, scale) in comb) {
            when(s) {
                is TACSymbol.Const -> k_ += (s.value * scale * currScale)
                is TACSymbol.Var -> {
                    val key = LVar.PVar(s)
                    touched.add(key)
                    if(key in mut) {
                        mut[key] = (mut[key]!! + (scale * currScale))
                    } else {
                        mut[key] = scale * currScale
                    }
                }
            }
        }
        for(k in touched) {
            val c = mut[k]!!
            if(c == BigInteger.ZERO) {
                mut.remove(k)
            } else {
                mut[k] = c
            }
        }
        return LinearEquality(mut.build(), k_)
    }

    fun relates(synthRead: LVar.Instrumentation): Boolean =
        synthRead in term

    fun withConst(toMap: Map<LVar.PVar, BigInteger>): LinearEquality {
        var kAccum = this.k
        val newTerm = treapMapBuilderOf<LVar, BigInteger>()
        for((k, v) in this.term) {
            if(k !in toMap) {
                newTerm.put(k, v)
                continue
            }
            kAccum += v * toMap[k]!!
        }
        return LinearEquality(newTerm.build(), kAccum)
    }

    fun substSynthetic(concr: TACSymbol.Var, sym: LVar.Instrumentation): LinearEquality {
        check(sym in this.term)
        return this.copy(
                term = (term - sym) + (LVar.PVar(concr) to term[sym]!!)
        )
    }

    fun canGenFor(fv: TreapSet<TACSymbol.Var>, lhs: TACSymbol.Var) = relatesAny(fv) && (!relates(lhs) || lhs in fv)

    /**
     * Extract a [TACExpr] that expresses the information
     * that this [LinearEquality] provides in how [v] is defined.
     * For example, if this object represents the expression:
     *
     * `x - y - z = 0`
     *
     * And x is provided as the argument, this function will return y + z (as
     * this equality indicates x is equal to the addition of y and z).
     */
    fun definingIntEquationFor(v: TACSymbol.Var) : TACExpr? {
        val (terms, off) = definingCoeffAndOffsetFor(v) ?: return null
        val sub = mutableListOf<TACExpr>()
        val pos = mutableListOf<TACExpr>()
        for((k, c) in terms) {
            if(k !is LVar.PVar) {
                return null
            }
            val exp = if(c.abs() != BigInteger.ONE) {
                TACExpr.Vec.Mul(
                        c.asTACSymbol().asSym(),
                        k.v.asSym()
                )
            } else {
                k.v.asSym()
            }
            /* Opposite side of the equation */
            if(c < BigInteger.ZERO) {
                sub.add(exp)
            } else {
                pos.add(exp)
            }
        }
        val kAsTerm = off.abs().asTACSymbol().asSym()
        if(off != BigInteger.ZERO) {
            if (off < BigInteger.ZERO) {
                sub.add(kAsTerm)
            } else {
                pos.add(kAsTerm)
            }
        }
        if(pos.isEmpty()) {
            return null
        }
        val posTerm = if (pos.size == 1) {
            pos.single()
        } else {
            TACExpr.Vec.Add(pos)
        }
        return if(sub.isEmpty()) {
            posTerm
        } else if(sub.size == 1) {
            TACExpr.BinOp.Sub(posTerm, sub.first())
        } else {
            sub.fold(posTerm) { Curr, toSub ->
                TACExpr.BinOp.Sub(Curr, toSub)
            }
        }
    }
}

/**
 * Suppose that [newLhs] = f([op], [other]). Denote the relation represented by
 * this [LinearEquality] by R(x, y, ...). Let [op] be a variable related by `R`.
 *
 * Further, if there exists some term inv([newLhs], [other]) where under the post-assignment
 * valuation we have [op], then we will have R(x, y, ...)[op -> inv([newLhs], [other])] provided
 * the assignment to [newLhs] does not affect the value of any arguments in R _after_ the substitution
 * of [op]. If [newLhs] is not an argument, this is trivially true. If [newLhs] is an argument, the
 * only case where this is true is if [op] = [newLhs], where by we have the old value of [op] (i.e., [newLhs])
 * is given by inv([newLhs], [other]), i.e., a term w.r.t the new value of [newLhs].
 *
 * Under what conditions can we derive the inv term? Assuming f is invertible in the
 * first argument, a sufficient condition is that [other] != [newLhs].
 *
 * So, in sum, the function checks multiple conditions:
 * 1) [other] is not [newLhs]
 * 2) [op] is related by R (otherwise the substitution is meaningless)
 * 3) If [newLhs] is related by this equality, then [op] is [newLhs]
 */
@OptIn(ExperimentalContracts::class)
private fun LinearEquality.validSubstitutionTarget(newLhs: TACSymbol.Var, op: TACSymbol, other: TACSymbol): Boolean {
    contract {
        returns(true) implies (op is TACSymbol.Var)
    }
    return canSubstituteArg(newLhs, op) && other != newLhs
}

private fun LinearEquality.canSubstituteArg(newLhs: TACSymbol.Var, op: TACSymbol): Boolean {
    if (op !is TACSymbol.Var) {
        return false
    }
    if (LVar.PVar(op) !in term) {
        return false
    }
    return LVar.PVar(newLhs) !in term || newLhs == op
}

@OptIn(ExperimentalContracts::class)
private fun LinearEquality.validSubstitutionTarget(newLhs: TACSymbol.Var, op: TACSymbol) : Boolean {
    contract {
        returns(true) implies (op is TACSymbol.Var)
    }
    return this.canSubstituteArg(newLhs, op)
}
