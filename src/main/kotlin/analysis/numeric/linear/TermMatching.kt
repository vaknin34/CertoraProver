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

import analysis.numeric.linear.TermMatching.MatchSpec
import datastructures.stdcollections.*
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * Logic and builders for [MatchSpec] against a [LinearTerm].
 */
object TermMatching {
    sealed interface ToTerm {
        fun toTerm() : Builder.Term
    }
    sealed interface ToAtom : ToTerm {
        fun toAtom(): Builder.MatchAtom
        override fun toTerm(): Builder.Term {
            return Builder.Term(listOf(toAtom()), k = null)
        }
    }

    /**
     * A match spec, of the form kj + sum ki * vi = 0
     * where vi is either an *exact* variable xi or a named wildcard Wi, and ki is an exact constant ci, or a named wildcard Mi.
     *
     * The ki terms are represented via [Factor] and the vi terms are represented with [Sym].
     *
     * It is not expected you build instances of this class yourself, using the [Builder] provided DSL.
     */
    data class MatchSpec(val terms: List<Pair<Sym, Factor>>, val k: Factor)

    /**
     * A factor (ki in the notation of [MatchSpec]), either a known constant, or a wildcard.
     */
    sealed class Factor : ToTerm {
        /**
         * A wildcard (Mi in the notation of [MatchSpec]) that must match a constant. [name] is the wildcard name, [scale] can represent linear scales of the
         * factor (for example, you can represent `2 * _ * v`) with `Symbolic("...", 2, ...)`, and represent `- _ * v`
         * with `Symbolic("...", -1, ...)`
         *
         * [pred] is a predicate applied to any candidate value of the wildcard, if it returns false, the wildcard
         * is not matched against that value.
         */
        data class Symbolic(val name: String, val scale: BigInteger, val pred: (BigInteger) -> Boolean = { true }) : Factor()

        /**
         * An exact constant (ci in the notation of [MatchSpec])
         */
        data class Constant(val c: BigInteger) : Factor()

        override fun toTerm(): Builder.Term {
            return Builder.Term(listOf(), k = this)
        }
    }

    /**
     * A variable (vi in the notation of [MatchSpec]), either exact variable, or a named wildcard
     */
    sealed class Sym : ToAtom {
        /**
         * Named wildcard (Wi in the notation of [MatchSpec]). [pred] is applied to any [LVar]
         * considered to match this wildcard; if it returns false for that [LVar], it is not matched.
         */
        data class Symbolic(val name: String, val pred: (LVar) -> Boolean = { _ -> true}) : Sym()

        /**
         * Exact variable (xi in the notation of [MatchSpec])
         */
        data class Exact(val s: LVar) : Sym()

        override fun toAtom(): Builder.MatchAtom {
            return Builder.MatchAtom(this, one)
        }
    }

    /**
     * The binding of wildcard names to their matchees
     */
    data class Match(
        val symbols: Map<String, LVar>,
        val factors: Map<String, BigInteger>
    )

    private val one = Factor.Constant(BigInteger.ONE)
    private val neg : BigInteger = BigInteger.ONE.negate()
    private val bOne = BigInteger.ONE

    @Suppress("unused")
    interface Builder {
        data class MatchAtom(
            val s: Sym,
            val f: Factor
        ) : ToAtom {
            constructor(lv: LVar, f: Factor) : this(Sym.Exact(lv), f)
            constructor(v: TACSymbol.Var, f: Factor) : this(LVar.PVar(v), f)
            override fun toAtom(): MatchAtom {
                return this
            }
        }
        data class Term(
            val atoms: List<MatchAtom>,
            val k: Factor?
        ) : ToTerm {
            init {
                val seen = mutableSetOf<String>()
                val seenFact = mutableSetOf<String>()
                for((k, v) in atoms) {
                    if(k is Sym.Symbolic && !seen.add(k.name)) {
                        throw IllegalArgumentException("Duplicated matching variable symbol name ${k.name}")
                    }
                    if(v is Factor.Symbolic && !seenFact.add(v.name)) {
                        throw IllegalArgumentException("Duplicated matching factor symbol name ${v.name}")
                    }
                }
                atoms.mapNotNull {
                    (it.s as? Sym.Symbolic)?.name
                }
            }

            override fun toTerm(): Term {
                return this
            }
        }

        /**
         * Int semantics
         */
        // times
        operator fun Int.times(other: ToTerm) = this.toBigInteger() * other
        operator fun Int.times(other: LVar) = this.toBigInteger() * other
        operator fun Int.times(other: TACSymbol.Var) = this.toBigInteger() * other

        // minus
        operator fun Int.minus(other: LVar) = this.toBigInteger() - other
        operator fun Int.minus(other: ToTerm) = this.toBigInteger() - other
        operator fun Int.minus(other: TACSymbol.Var) = this.toBigInteger() - other

        // plus
        operator fun Int.plus(other: ToTerm) = this.toBigInteger() + other
        operator fun Int.plus(other: LVar) = this.toBigInteger() + other
        operator fun Int.plus(other: TACSymbol.Var) = this.toBigInteger() + other

        /**
         * Big int semantics
         */
        // times
        operator fun BigInteger.times(other: ToTerm) = other * this
        operator fun BigInteger.times(other: LVar) = MatchAtom(Sym.Exact(other), Factor.Constant(this))
        operator fun BigInteger.times(other: TACSymbol.Var) = MatchAtom(Sym.Exact(LVar.PVar(other)), Factor.Constant(this))

        // minus
        operator fun BigInteger.minus(other: ToTerm) = (other * -1) + this
        operator fun BigInteger.minus(other: LVar) = Term(listOf(MatchAtom(Sym.Exact(other), Factor.Constant(neg))), k = Factor.Constant(this))
        operator fun BigInteger.minus(other: TACSymbol.Var) = Term(listOf(MatchAtom(Sym.Exact(LVar.PVar(other)), Factor.Constant(neg))), k = Factor.Constant(this))

        // plus
        operator fun BigInteger.plus(other: ToTerm) = other + this
        operator fun BigInteger.plus(other: LVar) = Term(listOf(MatchAtom(Sym.Exact(other), one)), k = Factor.Constant(this))
        operator fun BigInteger.plus(other: TACSymbol.Var) = this + LVar.PVar(other)

        /**
         * ToTerm
         */
        // plus
        operator fun ToTerm.plus(other: Int) = this + other.toBigInteger()
        operator fun ToTerm.plus(other: TACSymbol.Var) = this + LVar.PVar(other)
        operator fun ToTerm.plus(other: LVar) = this + MatchAtom(Sym.Exact(other), one)
        operator fun ToTerm.plus(other: BigInteger) = this + Factor.Constant(other)
        operator fun ToTerm.plus(other: ToTerm) = this.toTerm().let { term ->
            val o = other.toTerm()
            Term(
                atoms = o.atoms + term.atoms,
                k = term.k?.let innerLet@{
                    if(o.k == null) {
                        return@innerLet it
                    }
                    when(it) {
                        is Factor.Constant -> if(o.k !is Factor.Constant) {
                            throw UnsupportedOperationException("Additive matching is not supported")
                        } else {
                            Factor.Constant(o.k.c + it.c)
                        }
                        is Factor.Symbolic -> throw UnsupportedOperationException("Additive matching is not supported")
                    }
                } ?: o.k
            )
        }

        fun TACSymbol.lift() : ToTerm = when(this) {
            is TACSymbol.Var -> Sym.Exact(LVar.PVar(this))
            is TACSymbol.Const -> Factor.Constant(this.value)
        }

        // times (constants only)
        operator fun ToTerm.times(other: BigInteger) = this.toTerm().let { t ->
            Term(
                atoms = t.atoms.map {
                    it.copy(
                        f = it.f * other
                    )
                },
                k = t.k?.times(other)
            )
        }
        operator fun ToTerm.times(other: Factor.Constant) = this * other.c
        operator fun ToTerm.times(other: Int) = this * other.toBigInteger()

        // minus
        operator fun ToTerm.minus(other: ToTerm) = (other * -1) + this
        operator fun ToTerm.minus(other: LVar) = this - MatchAtom(other, one)
        operator fun ToTerm.minus(other: BigInteger) = this - Factor.Constant(other)
        operator fun ToTerm.minus(other: Int) = this - other.toBigInteger()
        operator fun ToTerm.minus(other: TACSymbol.Var) = this - LVar.PVar(other)

        /**
         * TACSymbol.Var semantics
         */
        // plus
        operator fun TACSymbol.Var.plus(other: ToTerm) = other + this
        operator fun TACSymbol.Var.plus(other: TACSymbol.Var) = this + LVar.PVar(other)
        operator fun TACSymbol.Var.plus(other: LVar) = MatchAtom(this, one) + other
        operator fun TACSymbol.Var.plus(other: Int) = other + this
        operator fun TACSymbol.Var.plus(other: BigInteger) = other + this

        // times
        operator fun TACSymbol.Var.times(other: Int) = this * other.toBigInteger()
        operator fun TACSymbol.Var.times(other: BigInteger) = other * this
        operator fun TACSymbol.Var.times(other: Factor) = MatchAtom(this, other)

        // minus
        operator fun TACSymbol.Var.minus(other: ToTerm) = (other * -1) + this
        operator fun TACSymbol.Var.minus(other: TACSymbol.Var) = this + (other * - 1)
        operator fun TACSymbol.Var.minus(other: LVar) = (-1 * other) + this
        operator fun TACSymbol.Var.minus(other: Int) = this + other.toBigInteger()
        operator fun TACSymbol.Var.minus(other: BigInteger) = Term(listOf(MatchAtom(this, one)), k = Factor.Constant(other.negate()))

        /**
         * LVar
         */
        operator fun LVar.plus(other: ToTerm) = other + this
        operator fun LVar.minus(other: TACSymbol.Var) = this + (other * -1)
        operator fun LVar.times(other: Factor) = MatchAtom(Sym.Exact(this), other)
        operator fun LVar.minus(other: ToTerm) = (other * -1) + this

        operator fun Sym.times(other: Factor) = MatchAtom(this, other)
        operator fun Factor.times(other: Sym) = MatchAtom(other, this)
        operator fun Factor.times(other: TACSymbol.Var) = MatchAtom(Sym.Exact(LVar.PVar(other)), this)

        /**
         * "equality"
         */
        infix fun ToTerm.`=`(other: ToTerm) = this - other
        infix fun ToTerm.`=`(other: Int) = this `=` other.toBigInteger()
        infix fun ToTerm.`=`(other: BigInteger) = this - other
        infix fun ToTerm.`=`(other: TACSymbol.Var) = this - other
        infix fun ToTerm.`=`(other: TACSymbol) = when(other) {
            is TACSymbol.Var -> this - other
            is TACSymbol.Const -> this `=` other.value
        }
        infix fun ToTerm.`=`(other: LVar.PVar) = this - other
        infix fun ToTerm.`=`(other: LVar.Instrumentation) = this - other

        infix fun LVar.`=`(other: ToTerm) = this - other
        infix fun LVar.`=`(other: TACSymbol.Var) = this + (other * -1)
        infix fun LVar.`=`(other: LVar) = MatchAtom(this, one) - other
        infix fun LVar.`=`(other: Int) = this `=` other.toBigInteger()
        infix fun LVar.`=`(other: BigInteger) = MatchAtom(this, one) - other

        infix fun TACSymbol.Var.`=`(other: ToTerm) = this - other
        infix fun TACSymbol.Var.`=`(other: LVar.PVar) = other `=` this
        infix fun TACSymbol.Var.`=`(other: TACSymbol.Var) = other - this
        infix fun TACSymbol.Var.`=`(other: Int) = this `=` other.toBigInteger()
        infix fun TACSymbol.Var.`=`(other: BigInteger) = this - other

        infix fun Int.`=`(other: ToTerm) = this - other
        infix fun Int.`=`(other: LVar.PVar) = other `=` this
        infix fun Int.`=`(other: TACSymbol.Var) = other - this

        infix fun BigInteger.`=`(other: ToTerm) = this - other
        infix fun BigInteger.`=`(other: LVar.PVar) = other `=` this
        infix fun BigInteger.`=`(other: TACSymbol.Var) = other - this

        operator fun Factor.Constant.times(other: BigInteger) = Factor.Constant(this.c * other)
        operator fun Factor.times(other: BigInteger) = when (this) {
            is Factor.Constant -> this * other
            is Factor.Symbolic -> this * other
        }
        operator fun Factor.Symbolic.times(other: BigInteger) = this.copy(
                    scale = this.scale * other
        )


        fun v(str: String, pred: (LVar) -> Boolean = { true }) = Sym.Symbolic(str, pred)
        fun k(str: String, pred: (BigInteger) -> Boolean = { true }) = Factor.Symbolic(str, scale = BigInteger.ONE, pred)
        fun n(str: String) = k(str) {
            it >= BigInteger.ZERO
        }
    }

    private infix fun BigInteger.fastMult(other: BigInteger) : BigInteger {
        return if(other === neg) {
            return if(this === bOne) {
                other
            } else if(this === neg) {
                bOne
            } else {
                this.negate()
            }
        } else if(other === bOne) {
            this
        } else if(this === bOne) {
            other
        } else if(this === neg) {
            other.negate()
        } else {
            this * other
        }
    }

    private infix fun BigInteger.fastDiv(other: BigInteger) : BigInteger {
        return if(other === bOne) {
            this
        } else if(other === neg) {
            this.negate()
        } else {
            this / other
        }
    }

    private fun BigInteger.fastAbs() = if(this === bOne || this == bOne) {
        bOne
    } else if(this === neg || this == neg) {
        bOne
    } else {
        this.abs()
    }

    private fun BigInteger.toMemo() = if(this == bOne) {
        bOne
    } else if(this == neg) {
        neg
    } else {
        this
    }

    /**
     * Attempts to match the specification represented by [this] against [other]. Put formally,
     * let the symbolic equation represented by this be normalized to:
     * kj + sum ki * vi = 0
     * where kj, ki, and vi have the interpretation as in [MatchSpec].
     *
     * The process of matching is then finding a rational scale r, and substitutions vsub {Wi -> xi} ksub {Mi -> ci} such that
     * r * ksub(vsub(sum ki * vi)) = other
     *
     * Where ksub(...) and vsub(...) denote applying the substituions to the arguments. On a successful match, vsub and ksub
     * are returned (in the form of the [Match] object). If there is no match (or the match is ambiguous), this returns null.
     */
    fun MatchSpec.matches(other_: LinearEquality) : Collection<Match> {
        val other = other_.canonicalize()
        if(this.terms.size != other.term.size) {
            return listOf()
        }
        if(this.k is Factor.Constant && this.k.c != BigInteger.ZERO && other.k == BigInteger.ZERO) {
            return listOf()
        }
        /**
         * Finding r for the purposes of match (which is decomposed into localNum and localDenom) is crucial to the
         * matching, and it is what we try to resolve first. Further, as matching variable wildcards is done through blind enumeration of
         * assignments, which requires m^n operations (m is the number of variables
         * in the linear term, and n is the number of wildcards), we eagerly match on exact variables, thereby minimizing m
         * (i.e., the number of candidates to try for each wildcard).
         *
         * In the following, (1), (2) etc. denote major steps of the algorithm which are marked later in the code
         *
         * Thus, we partition the terms ki * vi in this pattern into those where vi is exact vs symbolic terms (1).
         * We then iterate through the exact variables, seeing if the variable is mentioned in our target (2). If it is not,
         * we can bail out early. Otherwise, we check its factor ki (3). If it is constant, then we can either resolve
         * r (as r = a / ci, where a is the coefficient in [other]) (4), or determine there is no possible value for
         * r (r * a != ci) (5). Otherwise, we save the wildcard factor for later resolution (6).
         *
         * After processing all exact terms, we try to find vsub by enumerating all possibilities. This takes the form
         * of a loop that tries different possible assignments, and tries to find a "contradiction", i.e., an assignment
         * of Wi -> xi such that r * a != ki. Note that, by design, we only start resolving factor wildcards after determining
         * r (if we find this isn't possible, we declare the pattern is ambiguous and refuse to produce a match). In other words,
         * by the time we are trying to assign a wildcard variable to a concrete variable in [other], we must have r, which means
         * we can immediately discover such contradictions and fail early.
         *
         * The loop is pretty gnarly (it was written with the expectation this is called in several tight loops), so it is
         * documented elsewhere.
         *
         * After a "satisfying" wildcard assignment is found, we resolve the wildcards found in step 6 above (7). Note that,
         * if during the resolution of wildcards we discovered a value for r (8), this r could contradict some of
         * symbolic factors found in (6), so we can still still backtrack at this point. (9)
         *
         * This matcher returns eagerly, and will not enumerate multiple possible matches.
         *
         * Why do we canonicalize above? Well, it actually gives us that localDenom above must always be 1 for any r.
         * Why? by the definition of canonicalization, k and the coefficients of other must share no common factors
         * besides 1. suppose we had some localDenom > 1, and (localNum / localDenom) is fully reduced,
         * and (localNum / localDenom) * m gives an integer for all
         * m in codom(other.term) or m == other.k. But this means that localDenom divides localNum * m for all such m.
         * Because localNum / localDenom is fully reduced, localNum contains none of the prime factors of localDenom, meaning
         * that all of localDenoms prime factors must appear in m.
         * Thus localDenom must be a divisor for all such m, but after canonicalization the gcd of all m in other
         * must be one. Thus, localDenom will always be one!
         */

        /**
         * "residual" terms after exact matching, i.e. that need to be matched via k
         */
        val residue : MutableMap<Sym.Symbolic, Factor> = mutableMapOf()
        // exact variables matches with constant wildcards
        val subst : MutableMap<Factor.Symbolic, BigInteger> = mutableMapOf()
        var localNum: BigInteger? = null

        /**
         * Implements steps (4) and (5): if r is not set (localNum == null), sets r = scale / v (which must be an
         * integer), otherwise checks whether v * r = scale.
         */
        fun processMatch(scale: BigInteger, v: Factor.Constant): Boolean {
            if(localNum == null) {
                val vc = v.c.fastAbs()
                if(scale.mod(vc) != BigInteger.ZERO) {
                    return false
                }
                localNum = (scale fastDiv v.c).toMemo()
                return true
            }
            return localNum!! * v.c == scale
        }
        if(this.k is Factor.Constant) {
            if(this.k.c != BigInteger.ZERO) {
                if(!processMatch(other.k, this.k)) {
                    return listOf()
                }
            }
        } else {
            subst[this.k as Factor.Symbolic] = other.k
        }
        val visited = mutableSetOf<LVar>()
        /** step 1 - 6 */
        for((k, v) in this.terms) {
            if(k is Sym.Symbolic) {
                /** step (1) */
                residue[k] = v
            } else {
                check(k is Sym.Exact)
                /** step (2) */
                if(k.s !in other.term) {
                    return listOf()
                }
                val scale = other.term[k.s]!!
                /** step (3) */
                if(v is Factor.Constant) {
                    /** step 4 - 5 */
                    if(!processMatch(scale, v)) {
                        return listOf()
                    }
                } else {
                    if(v in subst) {
                        return listOf()
                    }
                    /** step (6) */
                    subst[v as Factor.Symbolic] = other.term[k.s]!!
                }
                visited.add(k.s)
            }
        }
        /**
         * The loop. Find all candidate terms, i.e., those terms that have not been matched by an exact term.
         * Put it into a list
         */
        val cands = other.term.filter {
            it.key !in visited
        }.entries.toList()

        /**
         * Get the residual terms into a sorted list, biasing those terms with constant factors first.
         * This guarantees that by the time we reach a variable wildcard with a constant wildcard, we will have
         * resolved r if at all possible (if we haven't we will bail out)
         */
        val res = residue.entries.sortedWith { a, b ->
            if(a.value is Factor.Constant && b.value !is Factor.Constant) {
                -1
            } else if(a.value !is Factor.Constant && b.value is Factor.Constant) {
                1
            } else {
                a.key.name.compareTo(b.key.name)
            }
        }
        check(cands.size == res.size)
        // too many candidates, this will both take *way* too long, and we can represent the assignments with a 32 bit int
        if(cands.size > 32) {
            return listOf()
        }
        /**
         * Step (7)
         * [st], if non-negative, indicates that index i in [res] gives the value of the wildcard
         * factor mentioned in `nm[st + i]` ([nm] is so called because it provides the "name" for the valuations
         * in [res]).
         *
         * [mk] is called only if factor matching succeeded, in which case it returns the substitution for variable
         * wildcards
         */
        fun resolveFactors(
            st: Int,
            res: Array<BigInteger>?,
            nm: List<Map.Entry<*, Factor>>?,
            mk: () -> Map<String, LVar>
        ) : Match? {
            if(localNum == null) {
                return null // ambiguous pattern (maybe)
            }
            val facts = mutableMapOf<String, BigInteger>()
            for((fact, scale) in subst) {
                val denomScale = fact.scale
                val actualScale = (scale fastMult localNum!!).takeIf {
                    it.mod(denomScale.fastAbs()) == BigInteger.ZERO
                }?.let {
                    it fastDiv denomScale
                } ?: return null
                if(!fact.pred(actualScale)) {
                    return null
                }
                facts[fact.name] = actualScale
            }
            res?.forEachIndexed { index, v ->
                facts[(nm!!.get(st + index).value as Factor.Symbolic).name] = v
            }
            return Match(
                factors = facts,
                symbols = mk()
            )
        }
        if(res.isEmpty()) {
            return resolveFactors(-1, null, null) {
                mapOf()
            }.let(::listOfNotNull)
        }
        /**
         * `st[j] == k` indicates that the residual term `res[j]` is being matched to `cand[k]`. -1 indicates
         * no assignment yet.
         */
        val state = Array(res.size) {
            -1
        }

        /**
         * Records that r is being set at the first element, or has been set prior to the loop (it is easy to verify
         * that either r will already be set, or must be set by the assignment of the first residual term
         */
        val setAt = if(localNum != null) {
            -1
        } else {
            0
        }

        /**
         * Bitvector set. if bit position i is set, it indicates that `cand[i]` has already been assigned
         */
        var taken = 0

        /**
         * The current residual item being worked on
         */
        var work = 0

        /**
         * If there are factor wildcards, record the assignments for those wildcards here. This array is non-null
         * only if there are any factor wildcards, and its size will be equal to the number of such terms.
         */
        var symbolAssign : Array<BigInteger>? = null

        val toReturn = mutableListOf<Match>()
        /**
         * Where, in the list `res`, the factor wildcards reside. The biasing in the sort algorithm above means that
         * the index of the first factor wildcard we see will be this value. symbolAssign is non-null iff this is non-negative
         */
        var symbolStart = -1
        while(work >= 0) {
            val term = res[work]
            if (localNum == null) {
                /**
                 * we haven't set r, and are in a position where we need to know it ahead of time
                 */
                if (term.value is Factor.Symbolic) {
                    return listOf()
                }
            }
            /**
             * if work == 0 == setAt, that means we're about to make a new attempt at finding a match for the first
             * wildcard, and this match will determine the value of r, thus discard the old value of r (if r was set
             * prior to this loop, setAt == -1 and this branch cannot be taken)
             */
            if(setAt == work) {
                localNum = null
            }
            /** If this is the first wildcard factor, initialize our datastructres */
            if(symbolStart == -1 && term.value is Factor.Symbolic) {
                symbolStart = work
                symbolAssign = Array(res.size - work) {
                    BigInteger.ZERO
                }
            }
            /**
             * If we are revisiting work due to a backtrack, clear our old "reservation" of st[work]
             */
            val currSt = state[work]
            if(currSt >= 0) {
                taken = taken xor (1 shl currSt)
            }
            /**
             * Skip ahead. If we are not visiting this via backtracking, st[work] == -1, so this means we will
             * start considering the first possible candidate. If we *are* visiting it via backtracking, this will
             * move us to the next candidate.
             */
            state[work]++
            /**
             * The loop condition iterates the possible assignments for work (as represented by `st[work]`),
             * trying to find the first such assignment such that:
             * 1. The candidate has not already been taken, as represented by the `st[work]` bit of taken not being set
             * 2. The variable is accepted by the the wildcard's filter, and
             * 3. The scale for the candidate is consistent with r
             *
             * For 3, if r is not set, then this *will* set r, but if r can be set this way, then the loop immediately
             * exits. Ditto, if the factor for the work term is symbolic, and we get a match, then
             * this updates the symbolAssign array, but will do so immediately after exiting the loop.
             */
            while (state[work] < cands.size && !(((1 shl state[work]) and taken) == 0 && term.key.pred(cands[state[work]].key) &&
                when(val tV = term.value) {
                    is Factor.Constant -> processMatch(cands[state[work]].value, v = tV)
                    is Factor.Symbolic -> {
                        check(localNum != null)
                        val m = cands[state[work]].value
                        val scaledNum = (m fastMult localNum!!)
                        val toDivide = tV.scale
                        if(scaledNum.mod(toDivide.fastAbs()) != BigInteger.ZERO) {
                            false
                        } else {
                            val assign = scaledNum fastDiv toDivide
                            if(tV.pred(assign)) {
                                symbolAssign!![work - symbolStart] = assign
                                true
                            } else {
                                false
                            }
                        }
                    }
                })) {
                /**
                 * if we enter this loop body, then the current candidate for work (i.e., the candidate at `st[work]` is no
                 * good, so keep looking
                 */
                state[work]++
            }
            /**
             * If we exited the loop because we *didn't* run out of candidates, advance the work pointer.
             */
            if(state[work] != cands.size) {
                /**
                 * If we are done, try to resolve the final factors.
                 */
                if(work == res.lastIndex) {
                    taken = taken or (1 shl state[work])
                    /**
                     * if resolveFactor returns non-null, then we have a match. Otherwise
                     * we have a "contradiction", and this falls through to the rollback case below (9)
                     */
                    resolveFactors(st = symbolStart, res = symbolAssign, nm = res) {
                        val ret = mutableMapOf<String, LVar>()
                        /**
                         * Generate the substitution from from the wildcards to the variable names
                         */
                        for((ind, assign) in state.withIndex()) {
                            ret[res[ind].key.name] = cands[assign].key
                        }
                        ret
                    }?.let {
                        toReturn.add(it)
                    }
                } else {
                    /**
                     * Otherwise, mark that this candidate is taken, and advance the work pointer
                     */
                    taken = taken or (1 shl state[work])
                    work++
                    continue
                }
            }
            /**
             * If we had a reserved candidate, unreserve it
             */
            if(state[work] > -1) {
                taken = taken xor (1 shl state[work])
            }
            /**
             * Reset the work back to -1, indicating that we haven't tried any candidates for this residual term yet
             */
            state[work] = -1
            /**
             * backtrack
             */
            work--
        }
        /**
         * If we reach this point, then we exited the loop because work < 0, i.e., we tried to backtrack from 0.
         * Thus, no matches
         */
        return toReturn
    }

    private object TheBuilder : Builder

    infix fun LinearInvariants.matches(f: Builder.() -> Builder.Term) : Collection<Match> {
        val spec = compile(f)
        return this matches spec
    }

    infix fun LinearEquality.matches(f: Builder.() -> Builder.Term) : Collection<Match> {
        val spec = compile(f)
        return this matches spec
    }

    infix fun LinearInvariants.matches(spec: MatchSpec) : Collection<Match> {
        val res = mutableSetOf<Match>()
        for(inv in this) {
            spec.matches(inv).let(res::addAll)
        }
        return res
    }

    infix fun LinearEquality.matches(spec: MatchSpec) : Collection<Match> {
        return spec.matches(this)
    }

    fun compile(f: Builder.() -> Builder.Term): MatchSpec {
        val d = TheBuilder.f()
        val spec = MatchSpec(
            terms = d.atoms.map {
                it.s to when(it.f) {
                    is Factor.Constant -> Factor.Constant(it.f.c.toMemo())
                    is Factor.Symbolic -> Factor.Symbolic(it.f.name, it.f.scale.toMemo(), it.f.pred)
                }
            },
            k = d.k ?: Factor.Constant(BigInteger.ZERO)
        )
        return spec
    }


    infix fun LinearInvariants.matchesAny(f: Builder.() -> Builder.Term) : Match? {
        return this.matches(f).firstOrNull()
    }
}
