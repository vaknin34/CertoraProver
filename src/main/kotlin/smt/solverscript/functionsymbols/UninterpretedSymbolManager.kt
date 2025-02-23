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
import tac.MetaMap
import tac.Tag
import vc.data.FunctionInScope
import vc.data.LExpression


class UninterpretedSymbolManager private constructor(
    // TODO freezing mechanism is duplicated with [LExpressionFactory]..
    private var constantsFrozen: Boolean,
    private var axiomatizedFrozen: Boolean,
    private var arraySelectFrozen: Boolean,
    private var userDefinedFunctionsFrozen: Boolean,
    private var uninterpretedSortsFrozen: Boolean,
    private val inUseFunctionSymbols: MutableMap<String, UninterpretedFunctionSymbol>,
    private val constantSymbols: MutableMap<String, ConstantSymbol>,
    private val axiomatizedSymbols: MutableMap<String, AxiomatizedFunctionSymbol>,
    private val arraySelectSymbols: MutableMap<String, ArraySelectFunctionSymbol>,
    private val userDefinedSymbols: MutableMap<String, UserDefinedFunctionSymbol>,
    private val uninterpretedSorts: MutableSet<Tag.UserDefined.UninterpretedSort>
) {
    constructor() : this(
        constantsFrozen = false,
        axiomatizedFrozen = false,
        arraySelectFrozen = false,
        userDefinedFunctionsFrozen = false,
        uninterpretedSortsFrozen = false,
        inUseFunctionSymbols = mutableMapOf(),
        constantSymbols = mutableMapOf(),
        axiomatizedSymbols = mutableMapOf(),
        arraySelectSymbols = mutableMapOf(),
        userDefinedSymbols = mutableMapOf(),
        uninterpretedSorts = mutableSetOf()
    )


    fun freezeConstants() {
        constantsFrozen = true
    }

    fun freezeAxiomatized() {
        axiomatizedFrozen = true
    }

    fun freezeArraySelects() {
        arraySelectFrozen = true
    }

    fun freezeUserDefinedFunctions() {
        userDefinedFunctionsFrozen = true
    }


    fun freezeUninterpretedSorts() {
        uninterpretedSortsFrozen = true
    }


    fun getOrConstructConstant(name: String, sort: Tag, meta: MetaMap?): LExpression.Identifier {
        check(!constantsFrozen || constantSymbols.containsKey(name))
        { "attempt to register fresh symbol ($name) in when manager is already frozen" }
        val constantSymbol = constantSymbols.getOrPut(name) { createConstantSymbol(name, sort) }
        check(constantSymbol.tag == sort) { "symbol $name was already registered with a different sort: ${constantSymbol.tag} vs $sort" }
        registerUseOfFunctionSymbol(constantSymbol)
        return LExpression.Identifier(constantSymbol.name, constantSymbol.tag, meta ?: MetaMap())
    }


    /** constant uf's we register as ConstantSymbols - the others's first-class occurrences we will eliminate later.. */
    fun getOrConstructGhostIdentifier(name: String, uf: FunctionInScope.UF, meta: MetaMap?): LExpression.Identifier {
        check(!constantsFrozen || constantSymbols.containsKey(name))
        { "attempt to register fresh symbol ($name) in when manager is already frozen" }
        return if (uf.paramSorts.isEmpty()) {
            val f = constantSymbols.computeIfAbsent(name) {
                ConstantSymbol(name, uf.asTag)
            }
            registerUseOfConstant(f)
            LExpression.Identifier(name, uf.asTag, meta ?: MetaMap())
        } else {
            getOrConstructConstant(name, Tag.GhostMap(uf.paramSorts, uf.returnSort), meta)
        }
    }

    private fun createConstantSymbol(name: String, sort: Tag) =
        ConstantSymbol(name, sort)

    fun registerUseOfFunctionSymbol(functionSymbol: UninterpretedFunctionSymbol) {
        @Suppress("REDUNDANT_ELSE_IN_WHEN")
        when (functionSymbol) {
            is AxiomatizedFunctionSymbol -> registerUseOfAxiomatizedFunctionSymbol(functionSymbol)
            is ArraySelectFunctionSymbol -> registerUseOfArraySelect(functionSymbol)
            is UserDefinedFunctionSymbol -> registerUseOfUserDefined(functionSymbol)
            is ConstantSymbol -> registerUseOfConstant(functionSymbol)
            // leaving this redundant [else] to get an error when we miss something here
            else -> {
                error(
                    "Failed to register function symbol " +
                            "-- untracked kind of function symbol? $functionSymbol / ${functionSymbol.javaClass}"
                )
            }

        }
    }

    fun registerUseOfUserDefined(functionSymbol: UserDefinedFunctionSymbol) {
        check(!userDefinedFunctionsFrozen || userDefinedSymbols.containsKey(functionSymbol.name))
        { "attempt to register fresh symbol (${functionSymbol.name}) in when manager is already frozen" }
        functionSymbol.signature.allOccurringSorts.filterIsInstance<Tag.UserDefined.UninterpretedSort>()
            .forEach { registerUninterpretedSort(it) }
        inUseFunctionSymbols[functionSymbol.name] = functionSymbol
        userDefinedSymbols[functionSymbol.name] = functionSymbol
    }

    fun registerUseOfConstant(functionSymbol: ConstantSymbol) {
        check(!constantsFrozen || constantSymbols.containsKey(functionSymbol.name))
        { "attempt to register fresh symbol (${functionSymbol.name}) in when manager is already frozen" }
        functionSymbol.signature.allOccurringSorts.filterIsInstance<Tag.UserDefined.UninterpretedSort>()
            .forEach { registerUninterpretedSort(it) }
        inUseFunctionSymbols[functionSymbol.name] = functionSymbol
        constantSymbols[functionSymbol.name] = functionSymbol
    }


    private fun registerUseOfAxiomatizedFunctionSymbol(functionSymbol: AxiomatizedFunctionSymbol) {
        check(!axiomatizedFrozen || axiomatizedSymbols.containsKey(functionSymbol.name))
        { "attempt to register fresh symbol (${functionSymbol.name}) in when manager is already frozen" }
        inUseFunctionSymbols[functionSymbol.name] = functionSymbol
        axiomatizedSymbols[functionSymbol.name] = functionSymbol
    }

    private fun registerUseOfArraySelect(functionSymbol: ArraySelectFunctionSymbol) {
        check(!arraySelectFrozen || arraySelectSymbols.containsKey(functionSymbol.name))
        { "attempt to register fresh symbol (${functionSymbol.name}) in when manager is already frozen" }
        inUseFunctionSymbols[functionSymbol.name] = functionSymbol
        arraySelectSymbols[functionSymbol.name] = functionSymbol
    }

    fun registerUninterpretedSort(sort: Tag.UserDefined.UninterpretedSort) {
        check(!uninterpretedSortsFrozen)
        { "attempt to register uninterpreted sort $sort when manager is already frozen" }
        uninterpretedSorts.add(sort)
    }

    fun getUninterpSorts(): Set<Tag.UserDefined.UninterpretedSort> = uninterpretedSorts

    /** Check whether the given name is already in use for a constant symbol */
    fun isConstantNameInUse(name: String) = name in constantSymbols

    fun getInUseFunctionSymbol(name: String): UninterpretedFunctionSymbol? {
        val constant = constantSymbols[name]
        if (constant != null) return constant
        val axiomatizedFs = axiomatizedSymbols[name]
        if (axiomatizedFs != null) return axiomatizedFs
        val arrayFs = arraySelectSymbols[name]
        if (arrayFs != null) return arrayFs
        val userDefFs = userDefinedSymbols[name]
        if (userDefFs != null) return userDefFs
        return null
    }

    fun isFunctionSymbolInUse(symbol: UninterpretedFunctionSymbol): Boolean = inUseFunctionSymbols[symbol.name] == symbol

    /** returns a deep-copy of [this] */
    fun copy(): UninterpretedSymbolManager {
        return UninterpretedSymbolManager(
            constantsFrozen,
            axiomatizedFrozen,
            arraySelectFrozen,
            userDefinedFunctionsFrozen,
            uninterpretedSortsFrozen,
            inUseFunctionSymbols.toMutableMap(),
            constantSymbols.toMutableMap(),
            axiomatizedSymbols.toMutableMap(),
            arraySelectSymbols.toMutableMap(),
            userDefinedSymbols.toMutableMap(),
            uninterpretedSorts.toMutableSet(),
        )
    }

    fun getTagOfConstantSymbol(name: String): Tag? =
        constantSymbols[name]?.tag

    fun changeTypeOfConstantSymbol(name: String, newType: Tag) {
        check(!constantsFrozen)
        { "cannot change type of a constant once they're frozen" }
        val cs = constantSymbols[name]

        check(cs != null)
        { "could not find symbol $name among the registered constants, but expected to" }
        val new = ConstantSymbol(name, newType)
        constantSymbols[name] = new
        inUseFunctionSymbols[name] = new
    }

}
