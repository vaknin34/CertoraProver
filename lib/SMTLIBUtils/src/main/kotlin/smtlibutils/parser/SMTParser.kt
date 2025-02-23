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

package smtlibutils.parser

import com.certora.smtlibutils.smtlib.LexerSMT
import com.certora.smtlibutils.smtlib.ParserSMT
import java_cup.runtime.ComplexSymbolFactory
import log.*
import smtlibutils.algorithms.Unletter
import smtlibutils.data.*
import smtlibutils.data.Cmd.*
import utils.*
import java.io.StringReader

private val logger = Logger(SMTLIBUtilsLoggerTypes.SMTLIBUTILS)

class SMTParser(val data: String) {
    constructor(data: List<String>): this(data.joinToString("\n"))

    private var smt: List<Cmd>? = null
    private var script: ISmtScript? = null

    /**
     * @param _script probably must use [SmtScript] here -- i.e. one that has a symbol table, otherwise, function symbols
     *    get the dummyrank... [Rank.Unknown]
     */
    fun parse(_script: ISmtScript = SmtScript()) {
        script = _script

        val reader = StringReader(data)
        val csf = ComplexSymbolFactory()
        val lexer = LexerSMT(csf, reader)
        val parser = ParserSMT(lexer, csf)
        parser.setSmtScript(script)
        val smtParsed: List<Cmd> = try {
            parser.parse().value.uncheckedAs<List<Cmd>>()
        } catch (e: Exception) {
            throw SmtParserException("failed to parse", e)
        }
        smt = smtParsed
        logger.debug { "SMT $smt" }
    }

    fun getSmt(): SMT = SMT(smt ?: error { "must call parse() first" })

    fun getSmtScript(): ISmtScript = script ?: error { "must call parse() first" }

    companion object {
        fun parseText(smtText: String, script: ISmtScript = SmtScript()): SMT {
            val parser = SMTParser(smtText)
            parser.parse(script)
            return parser.getSmt()
        }

        fun parseCmd(smtText: String, script: ISmtScript): Cmd {
            val parsed = parseText(smtText, script)
            check(parsed.cmds.size == 1)
            return parsed.cmds.first()
        }

        fun parseExp(smtText: String, script: ISmtScript): SmtExp {
            val cmd = parseCmd("(assert $smtText)", script)
            return (cmd as Assert).exp
        }

        /**
         * Note that get-value output is not standardized all that well, e.g., when querying for an uninterpreted
         * function's model. If there are hacks due to this, we try to put them here, rather than deeper inside SMTLib
         * infra.
         */
        fun parseValues(smtText: String, script: ISmtScript): Map<SmtExp, SmtExp> {
            val valDefItems = decomposeList(smtText)

            val valDefs = mutableListOf<ValDef>()
            valDefItems.forEach { singleValDef ->
                val valDefDecomposed = decomposeList(singleValDef)
                check(valDefDecomposed.size == 2) { "a value definition should have two items, lhs and rhs, got $valDefDecomposed" }
                val (lhs, rhs) = valDefDecomposed
                // the reason why we have to add quotation here is that some solvers (e.g. z3, iirc) remove it
                // internally and don't seem to add it back when returning the model
                //
                // however, we since we started supporting model querying for application terms, just taking the lhs
                // and quoting it if it's not a symbol is not good enough -- thus we assume that everything starting
                //  with a parenthesis is meant as an application term and also has nothing inside that need quoting
                //  --> I'm not terribly happy with this, but don't see an easy/elegant way around it so far ..
                val lhsQuoted =
                    if (lhs.startsWith("(")) {
                        lhs
                    } else {
                        SmtSymbolQuoter.quoteIfNecessary(lhs)
                    }
                val parser = SMTParser("((${lhsQuoted} $rhs))")
                try {
                    parser.parse(script)
                } catch (e: SmtParserException) {
                    logger.warn { "failed to parse counter example value from solver:\n$singleValDef" }
                    return@forEach
                }
                val smt = parser.getSmt()
                check(
                    smt.cmds.size == 1 ||
                            (smt.cmds.size == 2 && smt.cmds[1] is StatsCmd)
                ) // some tolerance for some extra text that we'll ignore..
                check(smt.cmds[0] is ValDefList)
                val vds = smt.cmds[0] as ValDefList
                check(vds.valDefs.size == 1)
                valDefs.add(vds.valDefs.first().let {
                    ValDef(it.exp, Unletter.unlet(it.value))
                })
            }

            // we only report the first of these errors as info, the others as debug
            var reportedNonLitValue = false
            val res = mutableMapOf<SmtExp, SmtExp>()

            if (script is SmtScript) {
                val sorter = Sorter(script)
                valDefs.forEach { (exp, value) ->
                    val expSorted = sorter.sort(exp)
                    if (value.isValueLiteral(script.symbolTable)) {
                        res[expSorted] = try {
                            sorter.sort(value)
                        } catch (e: Exception) {
                            logger.warn { "Failed to sort model value $value." }
                            value
                        }
                    } else if (isDontCareModel(exp, value)) {
                        // we could report this don't-care status to the user -- something to look into some time, maybe
                        logger.info { "the model seems to be reporting \"don't care\" for the expression \"$exp\", " +
                            "omitting the value from the results" }
                    } else {
                        val msg =  { "got the non-literal result \"$value\"  when executing (get-value (... $expSorted ...)) command." }
                        if (!reportedNonLitValue) {
                            logger.info(msg)
                            logger.info { "(only reporting the first occurrence here)" }
                            reportedNonLitValue = true
                        } else {
                            logger.debug(msg)
                        }
                        logger.trace { "for $exp (sort: ${expSorted.sort}) got the value $value" }
                    }
                }
                return res
            } else {
                valDefs.forEach { (exp, value) ->
                    if (value.isValueLiteral()) {
                        res[exp] = value
                    } else {
                        val msg =  { "got the non-literal result \"$value\"  when executing (get-value (... $exp ...)) command." }
                        if (!reportedNonLitValue) {
                            logger.info(msg)
                            logger.info { "(only reporting the first occurrence here)" }
                            reportedNonLitValue = true
                        } else {
                            logger.debug(msg)
                        }
                        logger.trace { "for $exp got the value $value" }
                    }
                }
                return res
            }
        }

        /**
         * Adhoc-ish function to determine whether the solver (only supporting z3 so far, here) is telling us that some
         * model entry is a "don't care", i.e., the model will remain a model no matter what value we choose from the
         * domain.
         * See online discussions on z3's `model.completion` flag for more background, e.g.,
         * https://github.com/Z3Prover/z3/issues/7264 .
         */
        private fun isDontCareModel(exp: SmtExp, value: SmtExp): Boolean {
            if (value is SmtExp.Apply &&
                value.fs.name is Identifier.Indexed &&
                value.fs.name.sym == "as-array" &&
                (value.fs.name as? Identifier.Indexed)?.indices?.first() == exp.toString()) {
                // z3 sometimes wraps arrays like this ... so attempting to catch that here (not so bad if it escapes us)
                // example for a get-value result like this:  `(unused (_ as-array unused))`
                return true
            }
            if (value == exp) {
                return true
            }
            return false
        }

        /**
         * Takes an smt-style list of items, e.g. `(<item1> <item2> ...)` where the items themselves wrapped in
         * parentheses, too.
         * Also cuts away smtlib line comments ( `;` and everything that follows).
         * E.g. input `"((x 13) (y 14))"`, ... will return `listOf("(x 13)", "(y 14)"]`.
         * @return a list of the individual items in the list
         */
        private fun decomposeList(smtList: String): List<String>  {
            val items = mutableListOf<String>()
            var currentItem = StringBuilder()
            var parenCounter = 0
            var quoted = false
            var comment = false
            smtList.forEach { c ->
                when (c) {
                    ';' ->
                        comment = true
                    '\n'->
                        comment = false
                    '|' -> {
                        quoted = !quoted
                    }
                    '(' -> {
                        if (!quoted && !comment) {
                            parenCounter++
                            if (parenCounter == 1) {
                                check(currentItem.isEmpty())
                                { "currentItem should be empty at this point but is $currentItem" }
                            }
                        }
                        if (parenCounter > 1 && !comment) {
                            currentItem.append(c)
                        }
                    }
                    ')' -> {
                        if (!comment && parenCounter > 1) {
                            currentItem.append(c)
                        }
                        if (!quoted && !comment) {
                            parenCounter--
                            if (parenCounter == 1) {
                                // finished one top-level list item
                                items.add(currentItem.toString())
                                currentItem = StringBuilder()
                            } else if (parenCounter == 0 && currentItem.isNotEmpty()) {
                                // save the last item if any (this happens when the last item was an identifier or literal
                                items.add(currentItem.toString())
                            }
                        }
                    }
                    ' ' -> {
                        if ((quoted || parenCounter > 1) && !comment) {
                            currentItem.append(c)
                        }
                        if (!quoted && !comment) {
                            if (parenCounter == 1) {
                                // finished one top-level list item
                                if (currentItem.isNotEmpty()) items.add(currentItem.toString())
                                currentItem = StringBuilder()
                            }
                        }
                    }
                    else -> {
                        if (!comment) {
                            currentItem.append(c)
                        }
                    }
                }
            }
            check(parenCounter == 0) { "string from solver not well-parenthesized: $smtList" }
            return items
        }
    }

    class SmtParserException(msg: String, cause: Throwable) : IllegalStateException(msg, cause)
}
