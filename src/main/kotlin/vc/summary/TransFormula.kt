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

package vc.summary

import datastructures.Bijection
import datastructures.MutableBijection
import smt.solverscript.LExpressionFactory
import smt.solverscript.functionsymbols.*
import tac.MetaMap
import utils.containsAny
import utils.uncheckedAs
import vc.data.*
import vc.data.tacexprutil.DefaultTACExprTransformer
import vc.data.tacexprutil.TACExprUtils
import vc.data.tacexprutil.subsFull

/**
 *
 * @param EXP type of expressions that are used to represent the transition formula
 * @param VAR type of the "program variables", what we use to represent the variables of the SSA'ed program
 * @param SYM variable type inside the transition formulas, inVars and outVars map instances of [VAR] to instances of this
 * @param TF type of the [TransFormula] itself
 *
 * @param outVars contains that, when doing a sequential composition between this and another [TransFormula], will be
 *   unified with the inVars of that formula.
 *   In particular this means that any variables that are dangling during a sequential composition (in outVars of the
 *   first formula but not in inVars of the second, and vice versa) are havocced, i.e., the value in the second formula
 *   is not constrained to be equal to the value in the first formula.
 * @param inVars see [outVars]
 * @param assignedVars variables that are assigned in the formula; there must be an entry in outVars for each
 *    assignedVar, and it is an invariant, that that outVars get's a fresh SSA-instance within this formula,
 *     (NB this does not implicate that the fresh version is not constrained, or that that constraint does not
 *      depend on the old version of the variable)
 * @param auxVars all the variables in [exp] that are neither an in- nor an outVar
 *
 *
 */
abstract class TransFormula<EXP, VAR, SYM : EXP, TF : TransFormula<EXP, VAR, SYM, TF>> {
    abstract val exp: EXP
    abstract val inVars: Bijection<VAR, SYM>
    abstract val outVars: Bijection<VAR, SYM>
    abstract val auxVars: Set<SYM>
    abstract val assignedVars: Set<VAR>

    fun getAllVars(): Set<SYM> = inVars.values.toSet() + outVars.values.toSet() + auxVars

    /**
     * Notes:
     *  - This lifts the notion of logical substitution to [TransFormula]s.
     *  - The substitution mapping maps from symbols (i.e. variables, allegedly ocurring in the substituted formula) to
     *    to [TransFormula]s. The convention is that whenever a substitution happens, the vars-fields of the
     *    transformula are added to the new substitution result. The caller is responsible that the result is a well-
     *    formed [TransFormula].
     *
     */
    open class Substitutor<EXP, VAR, SYM : EXP, TF : TransFormula<EXP, VAR, SYM, TF>>(
        private val substitution: Map<SYM, TF>,
        private val getVariables: (EXP) -> Set<SYM>,
        private val symExpSubstitutor: (Map<SYM, EXP>, EXP) -> EXP,
        private val constructTransFormula: (EXP, Bijection<VAR, SYM>, Bijection<VAR, SYM>, Set<VAR>, Set<SYM>) -> TF
    ) {

        fun transform(transFormula: TF): TF {
            if (substitution.isEmpty()) return transFormula

            val newInVars = MutableBijection<VAR, SYM>()
            val newOutVars = MutableBijection<VAR, SYM>()
            val newAuxVars = mutableSetOf<SYM>()
            val newAssignedVars = mutableSetOf<VAR>()


            val allExpVars = transFormula.getAllVars()

            /* compute new inVars/outVars/auxVars */
            allExpVars.forEach { v ->
                var isInOrOut = false

                val subsRes = substitution[v]

                val matchingInVarPairs =
                    transFormula.inVars.filter { (_, tacVar) -> tacVar == v }
                if (matchingInVarPairs.isNotEmpty()) {
                    check(matchingInVarPairs.size == 1)
                    val matchingInVarPair = matchingInVarPairs.entries.first()

                    check(matchingInVarPair.value == v) { "this is the case ... right?.." }

                    if (subsRes == null) {
                        /* substitution has no entry --> symbol won't be subject to substitution --> leave as is */
                        newInVars[matchingInVarPair.key] = matchingInVarPair.value
                    }
                    isInOrOut = true
                }
                val matchingOutVarPairs =
                    transFormula.outVars.filter { (_, tacVar) -> tacVar == v }
                if (matchingOutVarPairs.isNotEmpty()) {
                    check(matchingOutVarPairs.size == 1)
                    val matchingOutVarPair = matchingOutVarPairs.entries.first()

                    check(matchingOutVarPair.value == v) { "this is the case ... right?.." }

                    if (subsRes == null) {
                        /* substitution has no entry --> symbol won't be subject to substitution --> leave as is */
                        newOutVars[matchingOutVarPair.key] = matchingOutVarPair.value
                    }

                    isInOrOut = true
                }

                if (!isInOrOut) {
                    check(transFormula.auxVars.contains(v)) { "TransFormula class invariant violated -- every occurring variable must be an in- out- or auxVar" }
                    if (subsRes == null) {
                        /* substitution has no entry --> symbol won't be subject to substitution --> leave as is */
                        newAuxVars.add(v)
                    }
                }

                if (subsRes != null) {
                    newOutVars.putAll(subsRes.outVars)
                    newInVars.putAll(subsRes.inVars)
                    newAuxVars.addAll(subsRes.auxVars)
                    newAssignedVars.addAll(subsRes.assignedVars)
                }
            }

            val exp = symExpSubstitutor(
                substitution.mapValues { (_, tf) -> tf.exp },
                transFormula.exp
            )
            return constructTransFormula(
                exp,
                newInVars,
                newOutVars,
                /* assignedVars remain unchanged since they don't refer to [exp], but to "program variables"/TACSummaryVar */
                //transFormula.assignedVars,
                newAssignedVars,
                newAuxVars
            )
        }
    }

    companion object {

        /** Check some class invariants of [TransFormula] upon construction. Might be inefficient --> should be `false`
         * in master. (would be nice to be able to switch it on for regression tests automatically...)  */
        const val checkClassInvariant = false


        fun <EXP, VAR, SYM : EXP> classInvariant(
            tfInVars: Bijection<VAR, SYM>,
            tfAuxVars: Set<SYM>,
            tfOutVars: Bijection<VAR, SYM>,
            assignedVars: Set<VAR>,
            exp: EXP,
            getVariables: (EXP) -> Set<SYM>
        ): Boolean {

            // invars, outvars in the formula are disjoint with the auxvars (inVars and auxVars may overlap, e.g. in an assume command)
            if (tfInVars.values.containsAny(tfAuxVars)) {
                error("inVars and auxVars are not disjoint, intersection: ${(tfInVars.values intersect tfAuxVars)}")
            }
            if (tfOutVars.values.containsAny(tfAuxVars)) {
                error("outVars and auxVars are not disjoint, intersection: ${(tfOutVars.values intersect tfAuxVars)}")
            }

            assignedVars.forEach { av ->
                check(av in tfOutVars)
                { "all assigned vars must be outVars" }
                check(tfOutVars[av] != tfInVars[av]) {
                    "the invar-occurrence in the formula of an assigned var " +
                            "must be different from the outVar-occurrence"
                }
            }

            val allVariables = getVariables(exp)

            val unregisteredVars =
                allVariables.filter {
                    !tfInVars.values.contains(it) && !tfOutVars.values.contains(it) && !tfAuxVars.contains(
                        it
                    )
                }
            if (unregisteredVars.isNotEmpty()) {
                error("found a variable in the formula that is neither an invar nor outvar nor auxvar: $unregisteredVars")
            }
            return true
        }


        fun <EXP, VAR, SYM : EXP, TF : TransFormula<EXP, VAR, SYM, TF>> sequentialComposition(
            tfs: List<TF>,
            acc: DefinitionInliningSeqCompAccumulator<EXP, VAR, SYM, TF>,
            freshVarFactory: (Any, SYM) -> SYM,
            getVariables: (EXP) -> Set<SYM>,
            substituteSymExp: (Map<SYM, EXP>, EXP) -> EXP,
            conjoin: (List<EXP>) -> EXP,
            constructTransFormula: (EXP, Bijection<VAR, SYM>, Bijection<VAR, SYM>, Set<VAR>, Set<SYM>) -> TF
        ): TF =
            sequentialCompositionWithMetaInfo(
                tfs,
                acc,
                freshVarFactory,
                getVariables,
                substituteSymExp,
                conjoin,
                constructTransFormula
            ).tf

        /**
         *
         * @param doIdxOptimization whether to automatically optimize subexpressions like `(select i (store a i x))` to
         *    `x` in all to-be-inlined definitions
         */
        data class DefinitionInliningSeqCompAccumulator<EXP, VAR, SYM : EXP, TF : TransFormula<EXP, VAR, SYM, TF>>(
            private val definitions: MutableMap<VAR, TF> = mutableMapOf(),
            private val definitionCollector: (TF, Set<SYM>) -> Map<SYM, TF>,
            private val definitionSimplifier: (TF) -> TF,
            private val ssaDefinitions: MutableMap<SYM, TF> = mutableMapOf()
        ) {

            fun getSsaDefs(): Map<SYM, TF> = ssaDefinitions.toMap()

            fun getSubstitution(inVars: Bijection<VAR, SYM>): Map<SYM, TF> =
                definitions.flatMap { (k, v) -> if (inVars[k] == null) listOf() else listOf(inVars[k]!! to v) }.toMap()

            /**
             * Scan [tfUnified] for definitions. Enter those definitions into our store.
             *
             * Note that [tfUnified], as its name suggests, has/must have been alpha-renamed for the sequential
             * composition already, at this point.
             */
            fun updateDefinitions(tfUnified: TF) {
                val assignedVarToSymInFormula =
                    Bijection.fromMap(
                        tfUnified.assignedVars.associateWith { assignedVar ->
                            tfUnified.outVars[assignedVar] ?: error("assigned var must be an out var, right?..")
                        }
                    )
                val collected = definitionCollector(tfUnified, assignedVarToSymInFormula.values.toSet())
                ssaDefinitions.putAll(collected)

                val defs: Bijection<VAR, TF> =
                    Bijection.fromMap(
                        collected
                            .map { (k, v) -> assignedVarToSymInFormula.reverseGet(k!!)!! to v }
                            .toMap())
                defs.forEach { (k, v) ->
                    definitions[k] = definitionSimplifier(v)
                }
            }
        }

        /**
         * @param acc object that accumulates info over the conjuncts and massages the next-to-be-sequentially-composed
         *      transformula, can be used to inline definitions (for vanilla sequential composition, use the according
         *      Nop-accumulator)
         */
        fun <EXP, VAR, SYM : EXP, TF : TransFormula<EXP, VAR, SYM, TF>> sequentialCompositionWithMetaInfo(
            tfs: List<TF>,
            acc: DefinitionInliningSeqCompAccumulator<EXP, VAR, SYM, TF>,
            freshVarFactory: (Any, SYM) -> SYM,
            getVariables: (EXP) -> Set<SYM>,
            substituteSymExp: (Map<SYM, EXP>, EXP) -> EXP,
            conjoin: (List<EXP>) -> EXP,
            constructTransFormula: (EXP, Bijection<VAR, SYM>, Bijection<VAR, SYM>, Set<VAR>, Set<SYM>) -> TF,
            inputAlreadyInSsa: Boolean = false,
        ): SeqCompResult<EXP, VAR, SYM, TF> {
            check(tfs.isNotEmpty())

            val tfConjuncts = mutableListOf<EXP>()
            val tfAuxVars = mutableSetOf<SYM>()
            val tfInVars = MutableBijection<VAR, SYM>()
            val tfOutVars = MutableBijection<VAR, SYM>()
            val tfAssignedVars = mutableSetOf<VAR>()

            val varsOccurringInLhs = mutableSetOf<SYM>()

            /** used for model backtranslation;
             * background:
             * Sequential composition makes inVars and outVars into auxVars by unifying them.
             * These auxVars don't have a mapping to the program vars ([TACSummaryVar]) that they belonged to in the
             * resulting TransFormula.
             * In this mapping we store this information: Whenever an in/outvar becomes an auxVar through unification,
             * we add an entry, that stores the index (of the sequential composition item), the [TACSummaryVar]/[VAR] and
             * the auxVar that we introduced.
             */
            val indexToProgramVarToAuxVar = mutableMapOf<Pair<Int, VAR>, SYM>()

            if (tfs.size == 1) {
                acc.updateDefinitions(tfs[0])
                return SeqCompResult(tfs.first(), listOf(tfs.first().exp), mapOf(), acc.getSsaDefs())
            }

            tfs.forEachIndexed { index, currTf ->

                val auxVarSubs = mutableMapOf<SYM, TF>()
                currTf.auxVars.forEach {
                    if (it in tfAuxVars) {
                        val fv =
                            if (inputAlreadyInSsa) {
                                it
                            } else {
                                freshVarFactory(TACSymbol.Factory.AuxVarPurpose.COL, it)
                            }
                        auxVarSubs[it] =
                            constructTransFormula(fv, Bijection(), Bijection(), setOf(), setOf(fv))
                    }
                }
                val currWithAuxVarsRenamed =
                    Substitutor(auxVarSubs, getVariables, substituteSymExp, constructTransFormula).transform(currTf)

                // connect the in/outVars from prev and current
                val unifyResult: UnifyResult<EXP, VAR, SYM, TF> =
                    computeSequentialUnifyingSubstitution(tfOutVars, currWithAuxVarsRenamed, constructTransFormula)

                unifyResult.substitution.entries.forEach { (_, tfFragment) ->
                    tfFragment.inVars.forEach { (v, sym) ->
                        indexToProgramVarToAuxVar[Pair(index, v)] =
                            sym // this inVar will become an auxVar through SSAing... -- tracking the association with the program var here
                    }
                    check(tfFragment.outVars.isEmpty())
                    check(tfFragment.auxVars.isEmpty())
                    check(tfFragment.assignedVars.isEmpty())
                }


                /** each assigned var gets a fresh SSA representative */
                val assignedVarRenaming = currWithAuxVarsRenamed.assignedVars.map { tfSumVar ->
                    currWithAuxVarsRenamed.outVars[tfSumVar]!!.let { varInExp ->
                        val freshSsaVar =
                            if (inputAlreadyInSsa) {
                                varInExp
                            } else {
                                freshVarFactory(TACSymbol.Factory.AuxVarPurpose.SEQ, varInExp)
                            }
                        varInExp to
                                constructTransFormula(
                                    freshSsaVar,
                                    Bijection(),
                                    Bijection.fromMap(mapOf(tfSumVar to freshSsaVar)),
                                    setOf(tfSumVar),
                                    setOf()
                                )

                    }
                }.toMap()
                if (checkClassInvariant) {
                    check(!unifyResult.substitution.keys.containsAny(assignedVarRenaming.keys))
                }

                val unifyingAndAssignedVarRenamingSubs = unifyResult.substitution + assignedVarRenaming


                val tfUnified =
                    Substitutor(
                        unifyingAndAssignedVarRenamingSubs,
                        getVariables,
                        substituteSymExp,
                        constructTransFormula
                    ).transform(currWithAuxVarsRenamed)

                val newCurrTfOutVars = tfUnified.outVars
                    .map { (sumVar, expVar) ->
                        sumVar to (assignedVarRenaming[expVar] ?: expVar).uncheckedAs<SYM>()
                    }
                    .toMap()

                /**
                update acc:
                - for each assigned var, look for a single top-level-conjunctive definition (i.e. equality with the assigned var on one side)
                (if there is more than one definitions, or if the definition is under a disjunction, don't register it, underapproximating the definitions)
                - register the collected definitions
                 */
                acc.updateDefinitions(tfUnified)


                /** new in vars:
                 *  - start with the ones in the right-hand side formula
                 *  - subtract the ones that were unified
                 *     --> they're defined by the left-hand side formula, so don't connect to outvars from previous formulas
                 *  - add the invars from the left-hand side formula
                 *     --> they have precedence, thus add them on to the rhs ones (map [+] does overwrite existing keys)
                 */
                val newInVars = (tfUnified.inVars - unifyResult.unifiedVars)

                /** compute new aux vars */
                val newAuxVars = mutableSetOf<SYM>()

                newAuxVars.addAll(tfUnified.auxVars)

                check(newCurrTfOutVars.keys == tfUnified.outVars.keys)
                newCurrTfOutVars.keys
                    .filter { tacSumVar ->
                        val lhsVar: SYM? = tfOutVars[tacSumVar]
                        tacSumVar in tfOutVars.keys &&
                                lhsVar != newCurrTfOutVars[tacSumVar] &&
                                tfInVars[tacSumVar] != lhsVar &&
                                lhsVar in varsOccurringInLhs
                    }.forEach {
                        /** the outVar of the lhs is overwritten by the rhs
                         * and the variable is not an inVar of the lhs
                         * and the variable occurs in the formula
                         * --> it becomes an auxVar */
                        newAuxVars.add(tfOutVars[it]!!)
                    }

                tfUnified.inVars.keys
                    .filter {
                        it in tfOutVars.keys &&
                                it !in tfInVars.keys &&
                                it in newCurrTfOutVars &&
                                tfOutVars[it] != newCurrTfOutVars[it]
                    }.forEach {
                        newAuxVars.add(tfUnified.inVars[it]!!)
                    }

                // collected all data -- sort it into the right places for the overall formula
                tfAuxVars.addAll(newAuxVars)
                tfAuxVars.removeAll(newCurrTfOutVars.values)

                tfOutVars.putAll(newCurrTfOutVars)

                // the existing invars have precedence, since we're going left to right
                newInVars.forEach { (key: VAR, value: SYM) ->
                    if (key !in tfInVars.keys) tfInVars[key] = value
                }

                tfConjuncts.add(tfUnified.exp)

                varsOccurringInLhs.addAll(getVariables(tfUnified.exp))

                tfAssignedVars += tfUnified.assignedVars

                if (checkClassInvariant) {
                    classInvariant(
                        tfInVars,
                        tfAuxVars,
                        tfOutVars,
                        tfAssignedVars,
                        conjoin(tfConjuncts),
                        getVariables
                    )
                }
            }

            return SeqCompResult(
                constructTransFormula(conjoin(tfConjuncts), tfInVars, tfOutVars, tfAssignedVars, tfAuxVars),
                tfConjuncts,
                indexToProgramVarToAuxVar,
                acc.getSsaDefs()
            )
        }

        fun <EXP, VAR, SYM : EXP, TF : TransFormula<EXP, VAR, SYM, TF>> parallelComposition(
            tfs: List<TF>,
            getVariables: (EXP) -> Set<SYM>,
            substituteSymExp: (Map<SYM, EXP>, EXP) -> EXP,
            freshVarFactory: (Any, SYM) -> SYM,
            constructExpEquality: (EXP, EXP) -> EXP,
            disjoin: (List<EXP>) -> EXP,
            conjoin: (List<EXP>) -> EXP,
            constructTransFormula: (EXP, Bijection<VAR, SYM>, Bijection<VAR, SYM>, Set<VAR>, Set<SYM>) -> TF
        ): TF {
            val newInVars = MutableBijection<VAR, SYM>()
            val newOutVars = MutableBijection<VAR, SYM>()
            val newAssignedVars = tfs.flatMapTo(mutableSetOf()) { it.assignedVars }
            val newAuxVars = mutableSetOf<SYM>()

            /* rename apart aux vars in the different TransFormulas (... simply by making all fresh; there might be room
             * for optimization here..) */
            val tfsAuxVarsRenamed = tfs.map { tf ->
                val substitution = tf.auxVars.map { oldAuxVar ->
                    val freshVar = freshVarFactory(TACSymbol.Factory.AuxVarPurpose.COL, oldAuxVar)
                    newAuxVars.add(freshVar)
                    oldAuxVar to constructTransFormula(
                        freshVar,
                        Bijection(),
                        Bijection(),
                        setOf(),
                        setOf(freshVar)
                    )
                }.toMap()
                Substitutor(substitution, getVariables, substituteSymExp, constructTransFormula).transform(tf)
            }

            /* unify the inVar-Syms */
            val inVarToFreshSym: Map<VAR, SYM> = tfsAuxVarsRenamed.flatMap { it.inVars.entries }.map { (inVar, sym) ->
                val freshSym = freshVarFactory(TACSymbol.Factory.AuxVarPurpose.PAR, sym)
                newInVars[inVar] = freshSym
                inVar to freshSym
            }.toMap()
            val tfsInVarsUnified = tfsAuxVarsRenamed.map { tf ->
                val substitution = tf.inVars.map { (inVar, oldSym) ->
                    val freshSym = inVarToFreshSym[inVar] ?: error { "error in constructing the map??" }
                    oldSym to constructTransFormula(
                        freshSym,
                        Bijection.fromMap(mapOf(inVar to freshSym)),
                        Bijection.fromMap(
                            if (inVar in tf.outVars.keys) {
                                mapOf(inVar to freshSym)
                            } else {
                                mapOf()
                            }
                        ),
                        setOf(),
                        setOf()
                    )
                }.toMap()
                tf.outVars.forEach { v, _ ->
                    if (inVarToFreshSym.containsKey(v)) {
                        // v is also an outvar (as well as an inVar) in [tf] --> add it to newOutVars
                        newOutVars[v] = inVarToFreshSym[v]!!
                    }
                }
                Substitutor(substitution, getVariables, substituteSymExp, constructTransFormula).transform(tf)
            }


            /* for each tac-outvar introduce a fresh variable that will be the actual outVar, make the per-tf
             * outvars auxVars and assign them to the fresh outvar */
            val outVarToFreshSym = tfsInVarsUnified.flatMap { it.outVars.entries }.map { (outVar, sym) ->
                val freshSym = freshVarFactory(TACSymbol.Factory.AuxVarPurpose.PAR, sym)
                newOutVars[outVar] = freshSym
                outVar to freshSym
            }.toMap()
            val finalTfs = tfsInVarsUnified.map { tf ->
                /* construct the substitution, collect the equalities (`oldOutVar = freshOutVar`) that we want to append */
                val outVarEqualities = mutableListOf<EXP>()
                val outVarSymToFreshAuxVar = tf.outVars
                    .filter { (v, sym) -> tf.inVars[v] != sym } // treat outvars that are identical with an invar separately
                    .map { (outVar, oldSym) ->
                        /* replace the outVar-Syms by a fresh auxVar */
                        val oldSymFresh = freshVarFactory(TACSymbol.Factory.AuxVarPurpose.COL, oldSym)
                        newAuxVars.add(oldSymFresh)
                        val unifiedSym: SYM = outVarToFreshSym[outVar] ?: error("missing map entry?")
                        outVarEqualities.add(
                            constructExpEquality(
                                oldSymFresh,
                                unifiedSym
                            )
                        )
                        oldSym to constructTransFormula(
                            oldSymFresh,
                            Bijection(),
                            Bijection(),
                            // Bijection.fromMap(mapOf(outVar to unifiedSym)),
                            setOf(),
                            setOf(oldSymFresh)
                        )
                    }.toMap()

                tf.outVars
                    .filter { (v, sym) -> tf.inVars[v] == sym }
                    .forEach { (v, sym) ->
                        // outvar is identical with an invar, just equate the new parallel outvar to it (no need to make anything an auxVar or so)
                        val unifiedSym: SYM = outVarToFreshSym[v] ?: error("missing map entry?")
                        outVarEqualities.add(
                            constructExpEquality(
                                sym,
                                unifiedSym
                            )
                        )
                    }


                /* apply the substitution (replacing)the outVarSyms with the renamed-apart versions  */
                val tfOutVarsRenamed = Substitutor(
                    outVarSymToFreshAuxVar,
                    getVariables,
                    substituteSymExp,
                    constructTransFormula
                ).transform(tf)
                /* add the equalities to the formula */
                val conjunctionWithOutVarEqualties = listOf(tfOutVarsRenamed.exp) + outVarEqualities
                val tfOutVarEqualitiesAppended = constructTransFormula(
                    conjoin(conjunctionWithOutVarEqualties),
                    tfOutVarsRenamed.inVars,
                    newOutVars,
                    tfOutVarsRenamed.assignedVars,
                    tfOutVarsRenamed.auxVars
                )
                tfOutVarEqualitiesAppended
            }

            val newFormula = disjoin(finalTfs.map { it.exp })
            return constructTransFormula(newFormula, newInVars, newOutVars, newAssignedVars, newAuxVars)
        }

        /**
         * compute a TransFormula substitution that alpha-renames [r] in such a way that the inVars of [r] match their
         * corresponding outVars of [this]. An inVar corresponds to an outVar if their first entry, the [TACSummaryVar], matches.
         */
        fun <EXP, VAR, SYM : EXP, TF : TransFormula<EXP, VAR, SYM, TF>> computeSequentialUnifyingSubstitution(
            outVars: Bijection<VAR, SYM>,
            r: TF,
            constructTransFormula: (EXP, Bijection<VAR, SYM>, Bijection<VAR, SYM>, Set<VAR>, Set<SYM>) -> TF
        ): UnifyResult<EXP, VAR, SYM, TF> {
            val rSubstitution = mutableMapOf<SYM, TF>()
            val unifiedVars = mutableSetOf<VAR>()

            outVars.keys.forEach { tacVar: VAR ->
                if (tacVar !in r.inVars) return@forEach
                val subsVar = outVars[tacVar]!!
                rSubstitution[r.inVars[tacVar]!!] =
                    constructTransFormula(
                        subsVar,
                        Bijection.fromMap(mapOf(tacVar to subsVar)),
                        Bijection(),
                        setOf(),
                        setOf()
                    )
                unifiedVars.add(tacVar)
            }

            return UnifyResult(rSubstitution, unifiedVars)
        }

    }


}

/**
 * Represents a transition formula, i.e., a formula (Boolean-typed expression) that describes the effects of a program
 *  (statement, path, block, etc.) to the program variables.
 * Semantics:
 *  The [inVars] and [outVars] mappings are probably best thought of in terms of SSA-style variable versioning.
 *  All program variables that occur neither in [inVars] nor in [outVars] retain the same SSA-instance during the
 *  transition _and_ the transition does not further constrain them.
 *  If a program variable appears in [outVars], then the same variable version mapped in that pair will be used by
 *  the next subsequent transition that has that program variable in its [inVars]. On the other hand, if a variable
 *  in the transition formula does not occur in [outVars], that version/SSA-instance will not be used by a subsequent
 *  transition.
 *
 *
 * Examples:
 *
 * assignment 1
 *  x := x + 1
 *  exp:  x_13 = x_4 + 1
 *  inVars: x -> x_4
 *  outVars: x -> x_13
 *
 * assignment 2
 *  x := y / 2
 *  exp:  x_23 = y_4 / 2
 *  inVars: y -> y_4
 *  outVars: x -> x_23
 *
 * sequential composition 1
 *  x := x + 1 ; x := y / 2
 *  exp: x_13 = x_4 + 1 /\ x_23 = y_4 / 2
 *  inVar: x -> x_4, y -> y_4
 *  outVAr: x -> x_23
 *
 * sequential composition 2
 *  x := y / 2 ; x := x + 1
 *  exp: x_50 = (y_4 / 2) /\ x_13 = x_50 + 1
 *  inVar: y -> y_4
 *  outVAr: x -> x_13
 *  auxVars: { x_50 }
 *
 *
 */
data class TACTransFormula(
    override val exp: TACExpr,
    override val inVars: Bijection<TACSummaryVar, TACExpr.Sym.Var> = Bijection(),
    override val outVars: Bijection<TACSummaryVar, TACExpr.Sym.Var> = Bijection(),
    override val assignedVars: Set<TACSummaryVar> = setOf(),
    override val auxVars: Set<TACExpr.Sym.Var> = setOf(),
) : TransFormula<TACExpr, TACSummaryVar, TACExpr.Sym.Var, TACTransFormula>() {

    /** Just does `exp.toLExpression(..)` except that it preserves assignment information by inserting
     * `NonSMTInterpretedFunctionSymbol.Binary.AssignEq` (instead of normal `...Eq`) based on [assignedVars]. */
    fun toLExpression(lxf: LExpressionFactory, symbolTable: TACSymbolTable, meta: MetaMap? = null): LExpression {
        val assignedVarsLexp =
            assignedVars.mapTo(mutableSetOf()) { ToLExpression(it.sym.asSym(), lxf, symbolTable, meta) }
        val lExpNaive = ToLExpression(exp, lxf, symbolTable, meta)
        return lExpNaive.transformPost(lxf) {
            if (it.isApplyOf<TheoryFunctionSymbol.Binary.Eq>() && it.lhs in assignedVarsLexp) {
                lxf { it.lhs assignEq it.rhs }
            } else {
                it
            }
        }
    }

    init {
        if (checkClassInvariant) check(
            classInvariant(
                inVars,
                auxVars,
                outVars,
                assignedVars,
                exp,
                getVariables
            )
        ) { "class invariant violated" }
    }

    class Substitutor(substitution: Map<TACExpr.Sym.Var, TACTransFormula>) :
        TransFormula.Substitutor<TACExpr, TACSummaryVar, TACExpr.Sym.Var, TACTransFormula>(
            substitution,
            getVariables,
            substituteSymExp,
            constructTransFormula
        )


    companion object {
        val True
            get() = TACTransFormula(
                TACSymbol.True.asSym(),
                Bijection(),
                Bijection(),
                setOf(),
                setOf()
            )
        val False
            get() = TACTransFormula(
                TACSymbol.False.asSym(),
                Bijection(),
                Bijection(),
                setOf(),
                setOf()
            )


        val getVariables = { collectee: TACExpr ->
            collectee.subsFull.filterIsInstance<TACExpr.Sym.Var>().toSet()
        }

        private val substituteSymExp =
            { subs: Map<TACExpr.Sym.Var, TACExpr>, exp: TACExpr ->
                TACExprUtils.SubstitutorVar(subs).transformOuter(exp)
            }

        private val conjoin = { ls: List<TACExpr> -> TACExprFactUntyped.LAnd(ls) }

        private val disjoin = { ls: List<TACExpr> -> TACExprFactUntyped.LOr(ls) }

        private val constructTransFormula =
            { exp: TACExpr,
              inVars: Bijection<TACSummaryVar, TACExpr.Sym.Var>,
              outVars: Bijection<TACSummaryVar, TACExpr.Sym.Var>,
              assignedVars: Set<TACSummaryVar>,
              auxVars: Set<TACExpr.Sym.Var> ->
                TACTransFormula(exp, inVars, outVars, assignedVars, auxVars)
            }

        fun parallelComposition(vararg tfs: TACTransFormula) = parallelComposition(tfs.asList())

        fun parallelComposition(tfs: List<TACTransFormula>): TACTransFormula =
            parallelComposition(
                tfs.toList(),
                getVariables,
                substituteSymExp,
                { hook: Any, sym: TACExpr.Sym.Var ->
                    TACSymbol.Factory.getFreshAuxVar(
                        hook as TACSymbol.Factory.AuxVarPurpose,
                        sym.s
                    ).asSym()
                },
                { l: TACExpr, r: TACExpr -> TACExpr.BinRel.Eq(l, r) },
                disjoin,
                conjoin,
                constructTransFormula
            )


        fun sequentialComposition(vararg tfs: TACTransFormula, inputAlreadyInSsa: Boolean = false) =
            sequentialComposition(tfs.asList(), inputAlreadyInSsa)

        fun sequentialComposition(
            tfs: List<TACTransFormula>,
            inputAlreadyInSsa: Boolean = false
        ): SeqCompResult<TACExpr, TACSummaryVar, TACExpr.Sym.Var, TACTransFormula> =
            sequentialCompositionWithMetaInfo(
                tfs.toList(),
                TransFormula.Companion.DefinitionInliningSeqCompAccumulator(
                    definitionCollector =
                    { tf: TACTransFormula, defVars: Set<TACExpr.Sym.Var> ->
                        CollectDefinitionsTACExpr.computeDefinitions(tf, defVars)
                    },
                    definitionSimplifier = TACReadOverWriteAtSamePositionEliminator::transform
                ),
                { hook: Any, sym: TACExpr.Sym.Var ->
                    TACSymbol.Factory.getFreshAuxVar(
                        hook as TACSymbol.Factory.AuxVarPurpose,
                        sym.s
                    ).asSym()
                },
                getVariables,
                substituteSymExp,
                conjoin,
                constructTransFormula,
                inputAlreadyInSsa,
            )


    }
}

/**
 *
 * @param unifiedVars the [VAR]s  that were unified (i.e. their associated [SYM]s aligned) during unification
 *  */
data class UnifyResult<EXP, VAR, SYM : EXP, TF : TransFormula<EXP, VAR, SYM, TF>>(
    val substitution: Map<SYM, TF>,
    val unifiedVars: Set<VAR>
) {
    companion object {
//        val Empty = UnifyResult(mapOf(), mapOf())
    }
}

/*
 old doc, for more general `unify` function:
 * [lVarMap] and [rVarMap] map program variables to variables in a [TACTransFormula] each, we call the formulas l and r.
 * This method compute a substitution [rSubstitution] such that after applying [rSubstitution] to r the
 * formulas have the same internal variables for the intersected image of lVarMap and rVarMap
 *
 * Note the asymmetry: Only the formula belonging to [rVarMap] ("r") will need a substitution for the unification of
 *  the variables. Thus the caller can pick with of the to-be-connected-through-unification expressions can remain
 *   unchanged.
 */


data class LExpTransFormula(
    override val exp: LExpression,
    override val inVars: Bijection<TACSummaryVar, LExpression.Identifier>,
    override val outVars: Bijection<TACSummaryVar, LExpression.Identifier>,
    override val assignedVars: Set<TACSummaryVar>,
    override val auxVars: Set<LExpression.Identifier>
) : TransFormula<LExpression, TACSummaryVar, LExpression.Identifier, LExpTransFormula>() {
    init {
        if (checkClassInvariant) check(
            classInvariant(
                inVars,
                auxVars,
                outVars,
                assignedVars,
                exp,
                getVariables
            )
        ) { "class invariant violated" }
    }


    class Substitutor(substitution: Map<LExpression.Identifier, LExpTransFormula>) :
        TransFormula.Substitutor<LExpression, TACSummaryVar, LExpression.Identifier, LExpTransFormula>(
            substitution,
            getVariables,
            substituteSymExp,
            constructTransFormula
        )


    companion object {
        val True
            get() = LExpTransFormula(
                LExpression.Literal(true),
                Bijection(),
                Bijection(),
                setOf(),
                setOf()
            )
        val False
            get() = LExpTransFormula(
                LExpression.Literal(false),
                Bijection(),
                Bijection(),
                setOf(),
                setOf()
            )

        val getVariables = { collectee: LExpression ->
            collectee.getFreeIdentifiers()
        }

        private val substituteSymExp =
            { subs: Map<LExpression.Identifier, LExpression>, exp: LExpression -> exp.substitute(null, subs) }

        private val conjoin =
            { script: LExpressionFactory -> { ls: List<LExpression> -> script.and(ls) } }

        private val disjoin =
            { script: LExpressionFactory -> { ls: List<LExpression> -> script.or(ls) } }

        private val constructTransFormula = { exp: LExpression,
                                              inVars: Bijection<TACSummaryVar, LExpression.Identifier>,
                                              outVars: Bijection<TACSummaryVar, LExpression.Identifier>,
                                              assignedVars: Set<TACSummaryVar>,
                                              auxVars: Set<LExpression.Identifier> ->
            LExpTransFormula(exp, inVars, outVars, assignedVars, auxVars)
        }

        fun parallelComposition(vararg tfs: LExpTransFormula, script: LExpressionFactory) =
            parallelComposition(tfs.asList(), script)

        fun parallelComposition(tfs: List<LExpTransFormula>, script: LExpressionFactory):
                LExpTransFormula =
            parallelComposition(
                tfs.toList(),
                getVariables,
                substituteSymExp,
                { _, sym: LExpression.Identifier -> script.getSsaConstant(sym, null) },
                { l: LExpression, r: LExpression -> script.eq(l, r) },
                disjoin(script),
                conjoin(script),
                constructTransFormula
            )


        fun sequentialComposition(vararg tfs: LExpTransFormula, script: LExpressionFactory) =
            sequentialComposition(tfs.asList(), script)


        fun sequentialComposition(
            tfs: List<LExpTransFormula>, script: LExpressionFactory
        ): LExpTransFormula =
            sequentialComposition(
                tfs.toList(),
                TransFormula.Companion.DefinitionInliningSeqCompAccumulator<LExpression, TACSummaryVar, LExpression.Identifier, LExpTransFormula>(
                    definitionCollector =
                    { exp: LExpTransFormula, defVars: Set<LExpression.Identifier> ->
                        CollectDefinitionsLExp.computeDefinitions(
                            exp,
                            defVars
                        )
                    },
                    definitionSimplifier = { it } // no simplifications for LExpression case, for the moment -- might change in the future..
                ),
                { _, sym: LExpression.Identifier -> script.getSsaConstant(sym, null) },
                getVariables,
                substituteSymExp,
                conjoin(script),
                constructTransFormula
            )
    }
}

/**
 * see [TransFormula] for explanations of the type parameters
 */
data class SeqCompResult<EXP, VAR, SYM : EXP, TF : TransFormula<EXP, VAR, SYM, TF>>(
    val tf: TF,
    val conjuncts: List<EXP>,
    val substitution: Map<Pair<Int, VAR>, SYM>,
    val ssaDefinitions: Map<SYM, TF>
)


object TACReadOverWriteAtSamePositionEliminator {
    fun transform(tf: TACTransFormula): TACTransFormula {

        val expTransformer = object : DefaultTACExprTransformer() {
            override fun transformSelect(e: TACExpr.Select): TACExpr {
                val selectOverStoreTACExpr = SelectOverStoreTACExpr.fromExp(e)
                return if (selectOverStoreTACExpr != null &&
                    selectOverStoreTACExpr.selectIndex == selectOverStoreTACExpr.storeIndex
                ) {
                    selectOverStoreTACExpr.storedValue
                } else {
                    super.transformSelect(e)
                }
            }

        }

        val newExp = expTransformer.transform(tf.exp)

        val varsInNewExp = TACTransFormula.getVariables(newExp)

        val newInVars = Bijection.fromMap(tf.inVars.filter { (_, sym) -> sym in varsInNewExp })
        val newOutVars = Bijection.fromMap(tf.outVars.filter { (_, sym) -> sym in varsInNewExp })
        val newAssignedVars = tf.assignedVars.filter { v ->
            val outVar = tf.outVars[v] ?: "assigned var must be an out var -- Transformula broken?"
            outVar in varsInNewExp
        }.toSet()
        val newAuxVars = tf.auxVars.filter { sym -> sym in varsInNewExp }.toSet()

        return TACTransFormula(newExp, newInVars, newOutVars, newAssignedVars, newAuxVars)
    }


}

/**
 * A view on a TACExpr that matches the select-over-store pattern.
 *
 * Note: this could be an inline class, if it wasn't for the private constructor...
 */
class SelectOverStoreTACExpr private constructor(val exp: TACExpr.Select) {
    val store: TACExpr.Store
        get() = exp.base as TACExpr.Store
    val selectIndex: TACExpr
        get() = exp.loc
    val storeIndex: TACExpr
        get() = store.loc
    val storedValue: TACExpr
        get() = store.value

    companion object {
        fun fromExp(exp: TACExpr.Select): SelectOverStoreTACExpr? {
            return if (exp.base is TACExpr.Store) {
                SelectOverStoreTACExpr(exp)
            } else {
                null
            }
        }
    }
}

