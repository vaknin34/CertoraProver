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
import log.*
import smtlibutils.data.*
import smtlibutils.parser.SMTParser
import solver.CVC5SolverInfo
import utils.*
import java.io.Closeable
import java.util.concurrent.atomic.AtomicInteger

// Generous guardrails to prevent us from OOMing from large learned-lit clauses.
const val MAX_LEARNED_LIT_LEN = 10_000
const val MAX_LEARNED_LIT_TOTAL_LEN = 1_000_000

/**
 * Provides a medium-level abstraction of SMT solver interaction.
 *
 * Background:
 *  [SmtScript] manages expressions (via symbol table)
 *  [CmdProcessor] manages single commands (deals with parsing simple output, like `success`, hands out more complex output)
 *  [SmtQueryProcessor] manages queries (like "check this formula for sat"), allows fine-grained access if necessary
 */
class SmtQueryProcessor(initialScript: ISmtScript, val name: String, private val cmdProcessor: CmdProcessor) :
    Closeable {

    private var state = State.Init

    var script = initialScript

    val options = cmdProcessor.options

    /** Counter to identify each instance of this class. Here just for debugging purposes. */
    val serial = ctr.incrementAndGet()

    /* lower-level functionality */

    fun resetScript(script: SmtScript) {
        this.script = script
    }

    suspend fun reset(comment: String? = null) {
        if (cmdProcessor.options.incremental) {
            cmdProcessor.reset(comment)
            state = State.Init
        } else {
            close()
        }
    }

    suspend fun setLogic(cmd: Cmd.SetLogic) {
        cmdProcessor.setLogic(cmd)
    }

    suspend fun defineFun(cmd: Cmd.DefineFun) {
        cmdProcessor.process(cmd)
    }

    suspend fun declareSort(cmd: Cmd.DeclareSort) {
        cmdProcessor.process(cmd)
    }

    suspend fun declareDatatypes(cmd: Cmd.DeclareDatatypes) {
        cmdProcessor.process(cmd)
    }

    suspend fun declareFun(cmd: Cmd.DeclareFun) {
        cmdProcessor.process(cmd)
    }

    suspend fun assert(cmd: Cmd.Assert) {
        cmdProcessor.process(cmd)
    }

    suspend fun push(cmd: Cmd.Push = Cmd.Push(1)) {
        check(cmdProcessor.options.incremental) { "cmdProcessor $cmdProcessor not in incremental mode. push command is not available." }
        cmdProcessor.process(cmd)
    }

    suspend fun pop(cmd: Cmd.Pop = Cmd.Pop(1)) {
        check(cmdProcessor.options.incremental) { "cmdProcessor $cmdProcessor not in incremental mode. pop command is not available." }
        cmdProcessor.process(cmd)
    }

    suspend fun checkSat(comment: String? = null): SatResult {
        return SatResult.fromCheckSatOutput(
            cmdProcessor.checkSat(comment),
            cmdProcessor.solverInstanceInfo,
            cmdProcessor.options
        )
    }

    /**
     * Similar to [checkSat], but here we also parse literals that are learned by the solver during the solving,
     * i.e,. literals that are implied by the input formula.
     */
    suspend fun checkSatAndLearn(cmd: Cmd.CheckSat = Cmd.CheckSat()): Pair<SatResult, List<SmtExp>> {
        val output = cmdProcessor.checkSat(cmd.comment)

        var learnedLitTotalLength = 0

        //right now, we can parse only learned lits provided by CVC5 (we should check if other solvers provide them too)
        //hence, the parsing is now "hardcoded" here for CVC5 syntax. In future, we should build a LearnedLitsParser
        //abstract class with implementations for individual solvers (or put it elsewhere)
        val learnedLits = mutableListOf<SmtExp>()
        val processedOutput = output.onEach {
            val pattern = "(learned-lit "
            if (it.startsWith(pattern)){
                if (it.length > MAX_LEARNED_LIT_LEN) {
                    logger.warn { "$name: solver returned very long learned-lit ${it.substring(0, 100)}... (length=${it.length})" }
                } else if (learnedLitTotalLength + it.length > MAX_LEARNED_LIT_TOTAL_LEN) {
                    logger.warn { "$name: solver returned learned-lits totaling more than $MAX_LEARNED_LIT_TOTAL_LEN characters; ignoring some of them." }
                } else {
                    // these most like are not useful or not compatible between LIA and NIA
                    val badStuff = listOf("uninterp_mod", "uninterp_div", "SKOLEM_FUN", "skolem!", "linearIntDiv")
                    if (badStuff.none { pat -> it.contains(pat) }) {
                        var stripped = it.drop(pattern.length).dropLast(1)
                        // remove any annotation
                        stripped = stripped.substringBeforeLast(" :")
                        learnedLits += SMTParser.parseExp(stripped, script)
                        learnedLitTotalLength += it.length
                    }
                }
            }
        }

        val satResult = SatResult.fromCheckSatOutput(
            processedOutput,
            cmdProcessor.solverInstanceInfo,
            cmdProcessor.options
        )
        return satResult to learnedLits
    }

    fun getModel(comment: String? = null): Flow<String> {
        return cmdProcessor.processResult(Cmd.GetModel(comment))
    }

    suspend fun getValue(exp: SmtExp, symbolTable: SmtSymbolTable, comment: String? = null): SmtExp =
       getValue(listOf(exp), symbolTable, comment).values.single()

    suspend fun getValue(expList: List<SmtExp>, symbolTable: SmtSymbolTable, comment: String? = null): Map<SmtExp, SmtExp> {
        if (expList.isEmpty()) {
            // smt solver would complain if we passed an empty list in `(get-value ..)`
            return mapOf()
        }
        val output = cmdProcessor.processResult(script.getValue(expList).copy(comment = comment)).toList()
        return SMTParser.parseValues(output.joinToString("\n"), script.withSymbolTable(symbolTable))
    }


    suspend fun getUnsatCore(ucHelper: CoreHelper, comment: String? = null) {
        val output = cmdProcessor.getUnsatCore(comment).toList()
        ucHelper.parseCore(solverOutput = output)
    }

    suspend fun getUnknownReason(comment: String? = null): List<String> {
        return cmdProcessor.processResult(Cmd.GetInfo(":reason-unknown", comment)).toList()
    }

    suspend fun getDifficulties(comment: String? = null): List<String> {
        return cmdProcessor.processResult(
            Cmd.Custom("(get-difficulty)", expectsResult = true, comment = comment)
        ).toList()
    }

    /**
     * Calls `(get-timeout-core)` in the solver, will update ucHelper with the results of the call was a side effect.
     */
    suspend fun getTimeoutCore(ucHelper: CoreHelper) {
        check(this.cmdProcessor.solverInstanceInfo.solverConfig.solverInfo == CVC5SolverInfo) {
            "Timeout cores are only available from CVC5, currently. Got a (get-timeout-core) call on " +
                "solver with SolverInfo \"${cmdProcessor.solverInstanceInfo.solverConfig.solverInfo}\", and " +
                "SolverInstanceInfo name: \"${cmdProcessor.solverInstanceInfo.name}\"."
        }
        val output = cmdProcessor.processResult(
            Cmd.Custom("(get-timeout-core)", expectsResult = true)
        ).toList()
        ucHelper.parseCore(solverOutput = output)
    }

    override fun close() {
        cmdProcessor.close()
        state = State.Exited
    }

    suspend fun check(
        conjunction: List<HasSmtExp>,
        defineFuns: List<Cmd.DefineFun>,
        ucHelper: CoreHelper? = null
    ): SatResult {
        CmdProcessor.assertFormula(cmdProcessor, conjunction, script, defineFuns, ucHelper)
        return SatResult.fromCheckSatOutput(
            cmdProcessor.checkSat(),
            cmdProcessor.solverInstanceInfo,
            cmdProcessor.options
        )
    }

    suspend fun assertModel(modelAsDefineFuns: List<Cmd.DefineFun>) {
        check(state == State.Init) { "need to be in initial state to assert a model, but is in $state" }

        /* add define-funs from model  */
        modelAsDefineFuns.forEach { defineFun -> cmdProcessor.process(defineFun) }
        state = State.ModelAsserted
    }

    suspend fun eval(conjunction: Collection<SmtExp>): Boolean {
        check(state == State.ModelAsserted)

        push()

        /* assert clauses */
        conjunction.forEach {
            assert(script.assertCmd(it))
        }

        val res = checkSat()

        pop()

        return when (res) {
            SatResult.UNSAT -> false
            is SatResult.UNKNOWN -> error("got 'unknown' in model evaluation")
            is SatResult.SAT -> true
        }
    }

    override fun toString(): String {
        return "QueryProc($cmdProcessor)"
    }

    suspend fun process(cmd: Cmd) {
        when (cmd) {
            is Cmd.NoOp -> cmdProcessor.process(cmd)
            is Cmd.SetLogic -> setLogic(cmd)
            is Cmd.Assert -> assert(cmd)
            is Cmd.DefineFun -> defineFun(cmd)
            is Cmd.DeclareSort -> declareSort(cmd)
            is Cmd.DeclareFun -> declareFun(cmd)
            is Cmd.DeclareDatatypes -> declareDatatypes(cmd)
            is Cmd.Push -> push(cmd)
            is Cmd.Pop -> pop(cmd)
            is Cmd.CheckSat -> throw IllegalArgumentException("probably makes no sense to call check-sat without using the result, right?")
            is Cmd.GetModel -> throw UnsupportedOperationException("get model not yet supported properly")
            is Cmd.GetValue -> throw IllegalArgumentException("probably makes no sense to call getValue without using the result, right?")
            is Cmd.Custom -> cmdProcessor.process(cmd)
            else -> throw UnsupportedOperationException("command not supported $cmd")
        }
    }

   companion object {
        var ctr: AtomicInteger = AtomicInteger(0)

        suspend fun fromSolverInstanceInfo(
            solverInstanceInfo: SolverInstanceInfo,
            script: ISmtScript,
            dumpFile: String? = null
        ): SmtQueryProcessor {
            return SmtQueryProcessor(
                initialScript = script,
                name = solverInstanceInfo.name,
                cmdProcessor = ExtraCommandsCmdProcessor.fromCommand(
                    solverInstanceInfo.name,
                    solverInstanceInfo.actualCommand,
                    solverInstanceInfo.options,
                    solverInstanceInfo = solverInstanceInfo,
                    debugOutput = false,
                    dumpFile = dumpFile
                )
            )
        }

        @Suppress("ForbiddenMethodCall")
        fun reAddQuoting(
            symbolTable: SmtSymbolTable,
            linesRaw: Flow<String>
        ): Flow<String> {
            /* z3 drops the quotes ("|") from quoted symbols when outputting them --> restore them here for the quoted
             * symbols we know ... quite a hack, but hey... */
            val quotedFsNames =
                symbolTable
                    .getAllDeclaredFuns()
                    .filter { it.functionSymbol.name.toString().startsWith('|') }
                    .map { it.id.sym.substring(1, it.id.sym.length - 1) }
            val lines = linesRaw.map { line ->
                var newLine = line
                quotedFsNames.forEach { qfsn ->
                    newLine = newLine.replace("($qfsn ", "(|$qfsn| ")
                    newLine = newLine.replace("(define-fun $qfsn ", "(define-fun |$qfsn| ")
                    newLine = newLine.replace("(declare-fun $qfsn ", "(declare-fun |$qfsn| ")
                }
                newLine
            }
            return lines
        }

        /* utility functions */
        @Suppress("Unused") // may be come handy some time, since define-funs is the standard get-model format..
        suspend fun getModelAsDefineFuns(modelLinesRaw: Flow<String>, symbolTable: SmtSymbolTable): List<Cmd.DefineFun> {
            val modelLinesWithQuoting = reAddQuoting(symbolTable, modelLinesRaw).toList()

            val modelLines = modelKeywordHack(modelLinesWithQuoting)

            val smtParser = SMTParser(modelLines.joinToString("\n"))

            smtParser.parse()
            val cmds = smtParser.getSmt().cmds
            require(cmds.size == 1 && cmds.first() is Cmd.Model) { "expecting the input to this function to be of the form (model (define-fun ..)*) or ((define-fun .. )*), but got \"$modelLinesRaw\" "  }
            val modelCmd = cmds.first() as Cmd.Model
            return modelCmd.defs.map { it as Cmd.DefineFun }
        }

        /**
         * We restore the older (model ..) syntax. This is easier for us right now than to support parsing of 
         * the more recent syntax where the SMT solver omits the `model` keyword.
         */
        fun modelKeywordHack(modelLines: List<String>): List<String> =
            if (modelLines.first() == "(")
                listOf("(model") + modelLines.drop(1)
            else
                modelLines
    }

    enum class State { ModelAsserted, Init, Exited }

    private val logger = Logger(SMTLIBUtilsLoggerTypes.SMTLIBUTILS)
}
