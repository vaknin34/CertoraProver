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

package smt.solverscript.functionsymbols

import datastructures.stdcollections.*
import smt.FreeIdentifierCollector
import smt.GenerateEnv
import smt.solverscript.LExpressionFactory
import tac.isSubtypeOf
import tac.Tag
import utils.isInt
import vc.data.LExpression
import vc.data.LExpression.Identifier
import vc.data.LExpressionWithComment
import vc.summary.TransFormula
import java.math.BigInteger
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract

/**
 * Some LExpression extensions for ease of use.
 */

private fun LExpression.ApplyExpr.noAttribute(attrName: String): Nothing =
    error("Function Symbol ${f.javaClass} -- ${f.name} does not have a $attrName attribute")

/* checks this is an ApplyExpr and then runs [f] on it */
private inline fun <T> LExpression.asApply(f: LExpression.ApplyExpr.() -> T) =
    (this as? LExpression.ApplyExpr)?.let { it.f() }
        ?: error("Expression $this is not an ApplyExpr")

private inline fun <reified T : FunctionSymbol> simple(e: LExpression, argIndex: Int, attrName: String) =
    e.asApply {
        when (f) {
            is T -> args[argIndex]
            else -> noAttribute(attrName)
        }
    }


/* ITE */

val LExpression.cond
    get() = simple<TheoryFunctionSymbol.Ternary.Ite>(this, 0, "cond")

val LExpression.thenExp
    get() = simple<TheoryFunctionSymbol.Ternary.Ite>(this, 1, "thenExpr")

val LExpression.elseExp
    get() = simple<TheoryFunctionSymbol.Ternary.Ite>(this, 2, "elseExpr")


/* Select, Store */

val LExpression.isSelect
    get() = this is LExpression.ApplyExpr &&
        ((f is NonSMTInterpretedFunctionSymbol.MultiDimArray.MultiSelect) || (f is TheoryFunctionSymbol.Array.Select))

val LExpression.isStore
    get() = this is LExpression.ApplyExpr &&
        ((f is TheoryFunctionSymbol.Array.Store) || (f is NonSMTInterpretedFunctionSymbol.MultiDimArray.MultiStore))


val LExpression.map
    get() = asApply {
        when {
            isSelect || isStore -> args[0]
            else -> noAttribute("map")
        }
    }

val LExpression.loc
    get() = asApply {
        when (f) {
            is TheoryFunctionSymbol.Array.Select,
            is TheoryFunctionSymbol.Array.Store ->
                args[1]

            else -> noAttribute("loc")
        }
    }

val LExpression.locs
    get() = asApply {
        when {
            isSelect -> args.drop(1)
            isStore -> args.drop(1).dropLast(1)
            else -> noAttribute("locs")
        }
    }

val LExpression.value
    get() = asApply {
        when {
            isStore -> args.last()
            else -> noAttribute("locs")
        }
    }


/* LongStore */

val LExpression.dstMap
    get() = simple<AxiomatizedFunctionSymbol.LongStore>(this, 0, "dstMap")

val LExpression.dstOffset
    get() = simple<AxiomatizedFunctionSymbol.LongStore>(this, 1, "dstOffSet")

val LExpression.srcMap
    get() = simple<AxiomatizedFunctionSymbol.LongStore>(this, 2, "srcMap")

val LExpression.srcOffset
    get() = simple<AxiomatizedFunctionSymbol.LongStore>(this, 3, "srcOffset")

val LExpression.length
    get() = simple<AxiomatizedFunctionSymbol.LongStore>(this, 4, "length")


/* MapExpression */

val LExpression.mapDef
    get() = asApply {
        simple<AxiomatizedFunctionSymbol.MapDefinition>(this, args.size - 1, "mapDef")
    }

val LExpression.indVars
    get() = asApply {
        when (f) {
            is AxiomatizedFunctionSymbol.MapDefinition -> args.dropLast(1)
            else -> noAttribute("locs")
        }
    }


/* constants */

val LExpression.isConst
    get() = this is LExpression.Literal

val LExpression.asConstOrNull
    get() = when (this) {
        is LExpression.Literal -> this.i
        else -> null
    }

val LExpression.asConst
    get() = asConstOrNull ?: error("Expression $this is not a const")

val LExpression.asBoolConst
    get() = asConst != BigInteger.ZERO

infix fun LExpression.isEqTo(c: BigInteger) =
    asConstOrNull == c

infix fun LExpression.isEqTo(c: Int) =
    asConstOrNull == c.toBigInteger()

val LExpression.isTrue: Boolean
    get() = isConst && asBoolConst

val LExpression.isFalse: Boolean
    get() = isConst && !asBoolConst

val LExpression.isActuallyInt
    get() = isConst && asConst.isInt()

/** Whether this expression is a numeric literal. */
val LExpression.isNumericLiteral
    get() = this is LExpression.Literal && this.tag.isSubtypeOf(Tag.Int)

/* transformations */

/** Returns the original expression if it's not really changed (checked only via pointer comparison)
 *
 * This could return an [LExpression] that is not an [LExpression.ApplyExpr] in some odd cases like when
 * calling `f(false, x, y).copyFs(<LAnd>)` --> then the simplifications would kick in and just return `false`.
 */
fun LExpression.ApplyExpr.copyFs(lxf: LExpressionFactory, newFs: FunctionSymbol) =
    if (newFs == this.f) {
        this
    } else {
        lxf.applyExp(newFs, args, meta)
    }

/** Returns the original expression if it's not really changed (checked only via pointer comparison) */
fun LExpression.ApplyExpr.copyArgs(lxf: LExpressionFactory, newArgs: List<LExpression>) =
    if (this.args.size == newArgs.size && newArgs.zip(args).all { (a1, a2) -> a1 === a2 }) {
        this
    } else {
        lxf.applyExp(f, newArgs, meta)
    }

/** Returns the original expression if it's not really changed (checked only via pointer comparison) */
fun LExpression.QuantifiedExpr.copyBody(lxf: LExpressionFactory, newBody: LExpression) =
    if (this.body === newBody) {
        this
    } else {
        lxf.buildQuantifiedExpr(quantifier, quantifiedVar, newBody)
    }

/** Returns the original expression if it's not really changed (checked only via pointer comparison) */
fun LExpression.QuantifiedExpr.copyQuant(
    lxf: LExpressionFactory,
    newVars: List<Identifier> = this.quantifiedVar,
    newBody: LExpression = this.body,
) =
    if (this.body === newBody && this.quantifiedVar.toSet() == newVars.toSet()) {
        this
    } else {
        lxf.buildQuantifiedExpr(quantifier, newVars, newBody)
    }


/**
 * If [lxf] is null we don't use it to create new expressions. This is not recommended, and currently only used
 * in [TransFormula].
 */
fun LExpression.transformPost(lxf: LExpressionFactory?, transformer: (LExpression) -> LExpression): LExpression {
    fun rec(e: LExpression): LExpression = transformer(
        when (e) {
            is Identifier -> e
            is LExpression.Literal -> e
            is LExpression.ApplyExpr -> {
                val newArgs = e.args.map { rec(it) }
                if (lxf != null) {
                    e.copyArgs(lxf, newArgs)
                } else {
                    e.copy(args = newArgs)
                }
            }

            is LExpression.QuantifiedExpr -> {
                val newBody = rec(e.body)
                if (lxf != null) {
                    e.copyBody(lxf, newBody)
                } else {
                    e.copy(body = newBody)
                }
            }
        }
    )
    return rec(this)
}


/** Much like [transformPost], except applies the transformation before going into recursion */
fun LExpression.transformPre(lxf: LExpressionFactory, transformer: (LExpression) -> LExpression): LExpression {
    fun rec(exp: LExpression): LExpression = transformer(exp).let { e ->
        when (e) {
            is Identifier -> e
            is LExpression.Literal -> e
            is LExpression.ApplyExpr ->
                e.copyArgs(lxf, e.args.map { rec(it) })

            is LExpression.QuantifiedExpr ->
                e.copyBody(lxf, rec(e.body))
        }
    }
    return rec(this)
}


/**
 * Every subexpression that is a key in the [substitution] mapping is replaced by the corresponding value in the
 * [substitution] mapping.
 */
fun <T : LExpression> LExpression.substitute(lxf: LExpressionFactory?, substitution: Map<T, LExpression>) =
    transformPost(lxf) { substitution[it] ?: it }

/** * A variant of [substitute] that respects variable binding. */
fun LExpression.substituteQuantified(
    lxf: LExpressionFactory,
    substitution: Map<Identifier, LExpression>
): LExpression {
    fun rec(exp: LExpression, env: Set<Identifier>): LExpression =
        when (exp) {
            is LExpression.QuantifiedExpr ->
                exp.copyQuant(lxf, newBody = rec(exp.body, env + exp.quantifiedVar))
            is Identifier ->
                if (exp !in env && exp in substitution.keys) {
                    substitution[exp]!!
                } else {
                    exp
                }
            is LExpression.ApplyExpr ->
                exp.copyArgs(lxf, exp.args.map { rec(it, env) })
            is LExpression.Literal ->
                exp
        }
    return rec(this, setOf())
}


/* Traversal */

private fun subs(e: LExpression): Sequence<LExpression> = sequence {
    yield(e)
    when (e) {
        is LExpression.QuantifiedExpr -> yieldAll(subs(e.body))
        is LExpression.ApplyExpr -> e.args.forEach { yieldAll(subs(it)) }
        else -> Unit
    }
}

/** Sequence of sub expressions in preorder */
val LExpression.subs get() = subs(this)

/** Sequence of sub expressions in preorder */
val Iterable<LExpression>.subs get() = asSequence().flatMap { it.subs }

/** sequence of sub expressions of the expressions in the [Iterable] */
@get:JvmName("subs1")
val Iterable<LExpressionWithComment>.subs get() = asSequence().flatMap { it.lExpression.subs }

val Sequence<LExpressionWithComment>.subs get() = this.flatMap { it.lExpression.subs }

val Iterable<LExpressionWithComment>.expressionSequence get() = asSequence().map { it.lExpression }

/** Execute [f] on each sub-expression */
inline fun LExpression.traverse(f: (LExpression) -> Unit) = subs.forEach(f)


/** Execute [f] on each sub-expression, while also showing f the current quantified variables ([GenerateEnv]) in each
 * sub-expression. */
fun LExpression.traverseQuant(env: GenerateEnv = GenerateEnv(), f : (LExpression, GenerateEnv) -> Unit) {
    fun rec(e: LExpression, env: GenerateEnv) {
        f(e, env)
        when (e) {
            is LExpression.QuantifiedExpr -> rec(e.body, env.pushQuantifier(e))
            is LExpression.ApplyExpr -> e.args.forEach { rec(it, env) }
            else -> Unit
        }
    }
    rec(this, env)
}

/** Checks if [p] is true on any sub-expresssion */
inline fun LExpression.contains(p: (LExpression) -> Boolean) = subs.any(p)

/** Checks if [p] is true on any sub-expresssion */
fun Iterable<LExpression>.contains(p: (LExpression) -> Boolean) = subs.any(p)


/* misc */

@OptIn(ExperimentalContracts::class)
inline fun <reified T> LExpression?.isApplyOf(): Boolean {
    contract {
        returns(true) implies (this@isApplyOf is LExpression.ApplyExpr)
    }
    return this is LExpression.ApplyExpr && this.f is T
}


/** Returns all [Identifier] that appear in [this] expression and that aren't bound by a quantifier within
 * this expression. */
fun LExpression.getFreeIdentifiers(): Set<Identifier> =
    FreeIdentifierCollector(withCache = false).collect(this)

