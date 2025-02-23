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

package smt.axiomgenerators

import datastructures.stdcollections.*
import smt.solverscript.LExpressionFactory
import smt.solverscript.functionsymbols.AxiomatizedFunctionSymbol
import smt.solverscript.functionsymbols.IFixedFunctionSignatures.FixedFunctionSignatures
import smt.solverscript.functionsymbols.transformPre
import tac.Tag
import vc.data.LExpression
import vc.data.LExpressionWithEnvironment


typealias LExpressionWithEnvPair = Pair<LExpressionWithEnvironment, LExpressionWithEnvironment>


/**
 * Creates a LExpression-level representation of an SMT `define-fun`.
 * On creation registers itself in the factory.
 * (From there it will be added to the SMT file by [LExpressionToSmtLib].)
 */
open class LExpDefineFun(
    val lxf: LExpressionFactory,
    val name: String,
    val description: String,
    val tags: List<Tag>,
    val argNames: List<String>,
    outTag: Tag, // not used as a field now, so making it a parameter -- it's ok to change back to field once used
    val exp: LExpressionFactory.(List<LExpression>) -> LExpression
) {
    constructor(
        lxf: LExpressionFactory,
        name: String,
        description: String,
        tags: List<Tag>,
        outTag: Tag,
        exp: LExpressionFactory.(List<LExpression>) -> LExpression
    ): this(
        lxf, name, description, tags,
        tags.indices.map { 'a' + it }.map { "$it!$it" },
        outTag, exp
    )

    init {
        check(argNames.size == tags.size)
    }

    val symbol = AxiomatizedFunctionSymbol.DefFunc(name, FixedFunctionSignatures(tags, outTag))
    val params = argNames.zip(tags).map { (name, tag) -> lxf.buildVarForDef(name, tag) }
    val def = DefType(symbol, params, outTag, lxf.exp(params), description)

    init {
        lxf.registerFunctionSymbol(symbol)
        lxf.addDefFunc(this)
    }

    fun applyDef(vararg args: LExpression) =
        lxf.applyExp(symbol, *args)

    fun applyDef(args: List<LExpression> = emptyList()) =
        lxf.applyExp(symbol, args)

    fun applyDef(vararg args: LExpressionWithEnvironment) =
        quantifyIfNecessary(
            lxf.applyExp(symbol, args.map { it.exp }),
            *args
        )

    /**
     * If the expressions that we instantiated with were quantified, we want to quantify them again in the axiom.
     * Example:
     *  Say, we translate a formula 'forall x. x * y > 5'
     *  Then the subformula 'x * y' will be translated to 'uninterp_mul(x, y)' , and will trigger generation of axioms
     *   for 'uninterp_mul'.
     *  These axioms will talk about 'x'.
     *  Now, because 'x' was quantified in its context where we generated the axiom, it must be quantified again in the
     *  axiom (at least if we are doing the 'top-level axioms' strategy).
     *
     * @param instantiation instantiated axiom
     * @param lewes  [LExpressionWithEnvironment] objects that instantiation was instantiated with.
     */
    private fun quantifyIfNecessary(
        instantiation: LExpression,
        vararg lewes: LExpressionWithEnvironment
    ): LExpression {
        var res = instantiation
        lewes.forEach {
            res = lxf.forall(it.getQuantifiedVars().toList()) { res }
        }
        return res
    }

    /**
     * Replaces the placeholders in the definition with [args] and continues unfolding any definition it sees.
     */
    private fun unfold(args : List<LExpression>) =
        exp(lxf, args).transformPre(lxf) { e ->
            if (e !is LExpression.ApplyExpr) {
                e
            } else {
                lxf.getDefFunc(e.f.name)?.let {
                    it.exp(lxf, e.args)
                } ?: e
            }
        }

    fun unfold(vararg args: LExpression) =
        unfold(args.toList())
}

/**
 * Basically a [LExpDefineFun] that returns boolean.
 */
open class AxiomDef(
    lxf: LExpressionFactory,
    name: String,
    description: String,
    tags: List<Tag>,
    exp: LExpressionFactory.(List<LExpression>) -> LExpression
) : LExpDefineFun(lxf, "axiom_$name", description, tags, Tag.Bool, exp) {

    // These methods are protected so that each subclass wraps them in a function with the exact number of arguments.

    protected fun addAllToContainerInternal(
        axiomContainer: AxiomContainer,
        instances: Collection<List<LExpressionWithEnvironment>>
    ) =
        instances.forEach { args ->
            axiomContainer.addAxiom(applyDef(*args.toTypedArray()))
        }

    @JvmName("addAllToContainerInternal1")
    protected fun addAllToContainerInternal(axiomContainer: AxiomContainer, instances: Collection<List<LExpression>>) =
        instances.forEach { args ->
            axiomContainer.addAxiom(applyDef(*args.toTypedArray()), "")
        }
}


//------------------------------------------------------------------------------------------------

open class NullaryAxiomDef(
    lxf: LExpressionFactory,
    name: String,
    description: String,
    exp: LExpressionFactory.() -> LExpression
) : AxiomDef(lxf, name, description, listOf(), { _ -> exp() })


open class UnaryAxiomDef(
    lxf: LExpressionFactory,
    name: String,
    description: String,
    tag: Tag,
    exp: LExpressionFactory.(LExpression) -> LExpression
) : AxiomDef(lxf, name, description, listOf(tag), { l -> exp(l[0]) }) {

    fun addAllToContainer(axiomContainer: AxiomContainer, instances: Collection<LExpression>) {
        addAllToContainerInternal(axiomContainer, instances.map { listOf(it) })
    }

    @JvmName("addAllToContainer1")
    fun addAllToContainer(axiomContainer: AxiomContainer, instances: Collection<LExpressionWithEnvironment>) {
        addAllToContainerInternal(axiomContainer, instances.map { listOf(it) })
    }
}

open class BinaryAxiomDef(
    lxf: LExpressionFactory,
    name: String,
    description: String,
    tags: List<Tag>,
    exp: LExpressionFactory.(LExpression, LExpression) -> LExpression
) : AxiomDef(lxf, name, description, tags, { l -> exp(l[0], l[1]) }) {

    fun addAllToContainer(axiomContainer: AxiomContainer, instances: Collection<LExpressionWithEnvPair>) {
        addAllToContainerInternal(axiomContainer, instances.map { listOf(it.first, it.second) })
    }
}

open class QuadAxiomDef(
    lxf: LExpressionFactory,
    name: String,
    description: String,
    tags: List<Tag>,
    exp: LExpressionFactory.(LExpression, LExpression, LExpression, LExpression) -> LExpression
) : AxiomDef(lxf, name, description, tags, { l -> exp(l[0], l[1], l[2], l[3]) }) {
    fun addToContainer(
        axiomContainer: AxiomContainer,
        arg1: LExpressionWithEnvironment,
        arg2: LExpressionWithEnvironment,
        arg3: LExpressionWithEnvironment,
        arg4: LExpressionWithEnvironment,
    ) = addAllToContainerInternal(axiomContainer, listOf(listOf(arg1, arg2, arg3, arg4)))
}


//------------------------------------------------------------------------------------------------
// IntAxiomDefs

class UnaryIntAxiomDef(
    lxf: LExpressionFactory,
    name: String,
    description: String,
    exp: LExpressionFactory.(LExpression) -> LExpression
) : UnaryAxiomDef(lxf, name, description, Tag.Int, exp) {
    // Creates an axiom that is a conjunction of axioms
    constructor(lxf: LExpressionFactory, name: String, desc: String, axioms: Collection<UnaryIntAxiomDef>) :
            this(lxf, name, desc,
                { a -> lxf.and(axioms.map { it.applyDef(a) }) }
            )
}

class BinaryIntAxiomDef(
    lxf: LExpressionFactory,
    name: String,
    description: String,
    exp: LExpressionFactory.(LExpression, LExpression) -> LExpression
) : BinaryAxiomDef(lxf, name, description, listOf(Tag.Int, Tag.Int), exp) {
    // Creates an axiom that is a conjunction of axioms
    constructor(lxf: LExpressionFactory, name: String, desc: String, axioms: Collection<BinaryIntAxiomDef>) :
            this(lxf, name, desc,
                { a, b -> lxf.and(axioms.map { it.applyDef(a, b) }) }
            )
}

@Suppress("unused")
class QuadIntAxiomDef(
    lxf: LExpressionFactory,
    name: String,
    description: String,
    exp: LExpressionFactory.(LExpression, LExpression, LExpression, LExpression) -> LExpression
) : QuadAxiomDef(
    lxf,
    name,
    description,
    listOf(Tag.Int, Tag.Int, Tag.Int, Tag.Int),
    exp
) {
    // Create an axiom that is a conjunction of axioms
    constructor(lxf: LExpressionFactory, name: String, desc: String, axioms: Collection<QuadIntAxiomDef>) :
            this(lxf, name, desc,
                { a, b, c, d -> lxf.and(axioms.map { it.applyDef(a, b, c, d) }) }
            )
}


