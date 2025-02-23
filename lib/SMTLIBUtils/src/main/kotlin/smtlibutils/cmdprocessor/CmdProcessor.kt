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

package smtlibutils.cmdprocessor

import kotlinx.coroutines.flow.*
import smtlibutils.algorithms.CollectFunctionSymbols
import smtlibutils.algorithms.CollectQualIds
import smtlibutils.algorithms.CollectSorts.Companion.collectSorts
import smtlibutils.data.*
import utils.*
import java.io.Closeable

interface CmdProcessor : Closeable {

    val solverInstanceInfo: SolverInstanceInfo

    val options: Options
    val logic: Logic
        get() = options.logic

    // If you don't need the result, use `process` instead
    fun processResult(cmd: Cmd): Flow<String>

    fun checkSat(comment: String? = null) = processResult(Cmd.CheckSat(comment))
    suspend fun setLogic(cmd: Cmd.SetLogic) { process(cmd) }
    fun getUnsatCore(comment: String? = null) = processResult(Cmd.GetUnsatCore(comment))
    suspend fun reset(comment: String? = null) { process(Cmd.Reset(comment)) }

    companion object {

        suspend fun assertFormula(
            cmdP: CmdProcessor,
            conjunction: List<HasSmtExp>,
            script: ISmtScript,
            defineFuns: List<Cmd.DefineFun>,
            coreHelper: CoreHelper? = null
        ) = assertCmds(
                cmdP,
                conjunction.map { script.assertCmd(it.exp).copy(comment = (it as? SmtExpWithComment)?.comment) },
                script,
                defineFuns,
                coreHelper
        )

        /**
         *
         * @param unnamedToNamed if non-null, is filled with a mapping that associates raw expressions with their
         *  named version (only makes sense when [namer] is non-null, crashes otherwise)
         *
         * @param defineFuns sometimes a function must be defined, not just declared -- use this parameter for that
         *
         * TODO: unify with [SmtFormulaCheckerQuery.assertFormulaSmtLines] (?)
         */
        suspend fun assertCmds(
            cmdP: CmdProcessor,
            cmds: List<Cmd.Assert>,
            scriptIn: ISmtScript,
            defineFuns: List<Cmd.DefineFun>? = null,
            coreHelper: CoreHelper? = null
        ) {

            val script = scriptIn.withSymbolTable(SmtSymbolTable())// scriptIn.withSymbolTable(symbolTable)

            // delcare uninterpreted sorts
            collectSorts(cmds)
                .flatMap { it.getSortSymbols() }
                .filterIsInstance<SortSymbol.UserDefined>()
                .forEach { cmdP.process(script.declareSort(it.identifier.toString(), it.arity)) }

            // declare uninterpreted function symbols
            val cfs = CollectFunctionSymbols()
            cmds.forEach { cfs.cmd(it) }
            defineFuns?.forEach {
                // adding a quantification so the bound symbols of the definition are not collected as constants
                cfs.process(script.existsOrId(it.params, it.definition))
            }
            cfs.result
                .filterIsInstance<SmtUnintpFunctionSymbol>()
                .forEach { fs ->
                    check(!fs.rank.isParametrized()) {
                        "found a parametrized rank in a function symbol " +
                                "-- this method expects that all input terms have been sorted beforehand, that's not the case, right?"
                    }
                    val definition = defineFuns?.find { it.name.toString() == fs.name.toString() }
                    if (definition != null) {
                        // do nothing -- define-funs are added after all declarations
                    } else {
                        cmdP.process(
                            script.declareFun(
                                fs.name.toString(),
                                fs.rank.paramSorts,
                                fs.rank.resultSort
                            )
                        )
                    }
                }

            // declare constants
            val cqi = CollectQualIds()
            cmds.forEach { cqi.cmd(it) }
            defineFuns?.forEach {
                // adding a quantification so the bound symbols of the definition are not collected as constants
                cqi.process(script.existsOrId(it.params, it.definition))
            }
            cqi.result.forEach { qid ->
                val definition = defineFuns?.find { it.name == qid.toString() }
                if (definition == null) {
                    check(qid.sort != null)
                    /* no define-fun present for [qid] --> declare it */
                    cmdP.process(script.declareConst(qid.id.toString(), qid.sort))
                }
            }

            // add (define-fun ..)s
            defineFuns?.forEach {
                cmdP.process(it)
            }

            // assert cube
            processAssertCmds(cmdP, cmds.asSequence(), coreHelper)
        }

        /**
         * Process the assert commands in [cmds]: annotate them using [coreHelper] and pass them on to [cmdP].
         * [cmds] are only iterated a single time, thus taken as a sequence.
         */
        suspend fun processAssertCmds(
            cmdP: CmdProcessor,
            cmds: Sequence<Cmd.Assert>,
            coreHelper: CoreHelper? = null
        ) {
            cmds.forEach { cmd ->
                // note: we're doing the unsat core with cmd-granularity here --- need to revisit if we need something else
                val assertedExp = cmd.e

                val annotatedExp =
                        if (coreHelper != null) {
                            val name = coreHelper.nameToOriginal.reverseGet(assertedExp)
                            coreHelper.nameToAnnotated[name]!!
                        } else {
                            assertedExp
                        }

                val commentFromExp = when (annotatedExp) {
                    is SmtExpWithComment -> annotatedExp.comment
                    else -> null
                }

                cmdP.process(FactorySmtScript.assertCmd(annotatedExp.exp).copy(comment = commentFromExp))
            }
        }
    }

    sealed class Options {
        abstract val logic: Logic
        abstract val produceUnsatCores: Boolean
        abstract val produceModels: Boolean

        /**
         * This must be true if we want to use commands like push, pop, but also reset.
         * (E.g. yices does not accept reset in non-incremental mode; it also is sometimes faster in non-incremental
         *  mode. CVC4 does accept reset in non-incremental mode, but we're not distinguishing a reset-yes push/pop-no
         *  mode for now. )
         */
        abstract val incremental: Boolean

        /**
         * Some solvers don't support `(set-option :print-success true)`.
         * (We use this option when it's available since it's a safer interaction due to immediate feedback when a
         *  command has been processed.)
         */
        abstract val printSuccess: Boolean


        /**
        Some solvers expect to be used "one-off-style "

        they don't react to (check-sat) before they've written the whole file (vampire, alt-ergo) ..
        --> a downside of doing this here is that we cannot query for a model (or a :reason-unknown, or unsat core, etc)
        afterwards ... -- would need a rework to make this work with this class of solvers

        some print some stuff in addition to the sat result

         */
        abstract val oneOffSolver: Boolean

        /** We don't expect this [CmdProcessor] to give any answers, e.g., [PrintingCmdProcessor]. */
        abstract val noAnswers: Boolean

        /** Determines whether a [CmdProcessor] should track the "solver execution mode" as it is defined in the SMTLib
         * standard. See also [InteractingCmdProcessor.mode]. (We don't really use that feature, currently.) */
        abstract val trackModeInternal: Boolean

        abstract val queryUnknownReason: Boolean

        abstract val queryDifficulties: Boolean

        /** can't name this method `copy` due to overriding clash stuff .. */
        fun copy1(
                logic: Logic = this.logic,
                produceUnsatCores: Boolean = this.produceUnsatCores,
                produceModels: Boolean = this.produceModels,
                incremental: Boolean = this.incremental,
                printSuccess: Boolean = this.printSuccess,
                oneOffSolver: Boolean = this.oneOffSolver,
                noAnswers: Boolean = this.noAnswers,
                trackModeInternal: Boolean = this.trackModeInternal,
                queryUnknownReason: Boolean = this.queryUnknownReason,
                queryDifficulties: Boolean = this.queryDifficulties,
        ): Options {
            return when (this) {
                is Standard -> this.copy(
                        logic,
                        produceUnsatCores,
                        produceModels,
                        incremental,
                        printSuccess,
                        oneOffSolver,
                        noAnswers,
                        trackModeInternal,
                        queryUnknownReason,
                        queryDifficulties,
                )
                DontCare -> this
            }
        }

        data class Standard(
                override val logic: Logic,
                override val produceUnsatCores: Boolean,
                override val produceModels: Boolean = true,
                override val incremental: Boolean,
                override val printSuccess: Boolean = true,
                override val oneOffSolver: Boolean = false,
                override val noAnswers: Boolean = false,
                override val trackModeInternal: Boolean = false,
                override val queryUnknownReason: Boolean = true,
                override val queryDifficulties: Boolean = false,
        ) : Options()

        /** For use in [CmdProcessor]s for which the options in [Standard] don't apply. Currently only used for
         * [CollectingCmdProcessor]. */
        object DontCare : Options() {
            override val logic: Logic
                get() = throw UnsupportedOperationException("no options here, should not be queried")
            override val produceUnsatCores: Boolean
                get() = throw UnsupportedOperationException("no options here, should not be queried")
            override val produceModels: Boolean
                get() = throw UnsupportedOperationException("no options here, should not be queried")
            override val incremental: Boolean
                get() = throw UnsupportedOperationException("no options here, should not be queried")
            override val printSuccess: Boolean
                get() = throw UnsupportedOperationException("no options here, should not be queried")
            override val oneOffSolver: Boolean
                get() = throw UnsupportedOperationException("no options here, should not be queried")
            override val noAnswers: Boolean
                get() = throw UnsupportedOperationException("no options here, should not be queried")
            override val trackModeInternal: Boolean
                get() = throw UnsupportedOperationException("no options here, should not be queried")
            override val queryUnknownReason: Boolean
                get() = throw UnsupportedOperationException("no options here, should not be queried")
            override val queryDifficulties: Boolean
                get() = throw UnsupportedOperationException("no options here, should not be queried")
        }

        companion object {
            val BareBonesIncremental = Standard(
                    logic = Logic.ALL,
                    produceUnsatCores = false,
                    produceModels = false,
                    incremental = true,
                    printSuccess = false,
                    oneOffSolver = false,
                    noAnswers = false,
                    queryUnknownReason = false,
                    queryDifficulties = false,
            )

            val Default = Standard(
                    logic = Logic.ALL,
                    produceUnsatCores = false,
                    produceModels = true,
                    incremental = false,
                    printSuccess = false,
                    oneOffSolver = false,
                    noAnswers = false,
                    queryUnknownReason = true,
                    queryDifficulties = false,
            )

            fun reduceOptions(o1: Options, o2: Options): Options =
                    if (o1 == o2) {
                        o1
                    } else if (o1 is DontCare) {
                        o2
                    } else if (o1 !is DontCare) {
                        o1
                    } else {
                        throw IllegalStateException("cannot reduce contradicting options")
                    }

            fun fromQuery(smtFormulaCheckerQuery: SmtFormulaCheckerQuery, incremental: Boolean) =
                    Standard(
                            smtFormulaCheckerQuery.logic,
                            produceUnsatCores = smtFormulaCheckerQuery.info.getUnsatCore,
                            incremental = incremental,
                            queryDifficulties = smtFormulaCheckerQuery.info.getDifficulties,
                    )

        }
    }
}

// Defined as an extension because interfaces don't support "final" methods.  Override `processResult` instead.
suspend fun CmdProcessor.process(cmd: Cmd): Unit = processResult(cmd).collect()

