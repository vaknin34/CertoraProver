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

package analysis.smtblaster

import kotlinx.coroutines.flow.collect
import parallel.coroutines.onThisThread
import smtlibutils.cmdprocessor.*
import smtlibutils.data.*
import utils.*

class SmtExpScriptBuilder(
    private val termBuilder: AbstractSmtExpTermBuilder,
    private val cmdProcessor: CollectingCmdProcessor = CollectingCmdProcessor()
) : SmtScriptBuilder<Sort, SmtExp>(termBuilder) {

    private val script = termBuilder.script

    val cmdList: List<Cmd>
        get() =
//            if (script is SmtScript)  // TODO: is there a good place to have a sort check? -- this isn't it because sometimes this class is used for partial queries
//                Sorter(script).smt(cmdProcessor.getResult(declarationsFirst = true)).lines.map { it.toString() }
//            else
                cmdProcessor.getResult(declarationsFirst = true).cmds

    override fun declareFun(nm: String, args: List<Sort>, ret: Sort) {
        onThisThread { cmdProcessor.process(script.declareFun(nm, args, ret)) }
    }

    override fun SmtExp.implies(other: SmtExp): SmtExp {
        return script.apply(SmtIntpFunctionSymbol.Core.LImplies, this, other)
    }

    override fun forall(f: SmtScriptBuilder<Sort, SmtExp>.(SmtExp) -> SmtExp): SmtExp {
        val qVarNames = listOf("__arg1")
        // it's used, not sure why compiler complains here body is unused...
        @Suppress("UNUSED_EXPRESSION") val body = f(v.toIdent(qVarNames.first()))
        return mkdQuantified(qVarNames, body)
    }

    private fun mkdQuantified(qVarNames: List<String>, body: SmtExp): SmtExp.Quant.ForAll {
        val sortedVars = qVarNames.map { SortedVar(it, v.numericType) }
        return script.forAll(sortedVars, body)
    }

    override fun forall(f: SmtScriptBuilder<Sort, SmtExp>.(SmtExp, SmtExp) -> SmtExp): SmtExp {
        val qVarNames = listOf("__arg1", "__arg2")
        val ids = qVarNames.map { v.toIdent(it) }
        // it's used, not sure why compiler complains here body is unused...
        @Suppress("UNUSED_EXPRESSION") val body = f(ids[0], ids[1])
        return mkdQuantified(qVarNames, body)
    }

    override fun checkSat() {
        onThisThread {
            cmdProcessor.checkSat().collect()
        }
    }

    override fun declare(s: String, numericType: Sort) {
        onThisThread { cmdProcessor.process(script.declareConst(s, numericType)) }
    }

    override fun define(s: String, numericType: Sort, body: SmtExp) {
        onThisThread { cmdProcessor.process(script.defineFun(s, listOf(), numericType, body)) }
    }

    override fun addAssert(f: SmtExp) {
        onThisThread { cmdProcessor.process(script.assertCmd(f)) }
    }

    override fun fork(): SmtExpScriptBuilder {
        return SmtExpScriptBuilder(termBuilder.fork(), cmdProcessor.fork())
    }


    companion object {
        fun buildBVScript(preLoad: List<Cmd> = listOf(), f: SmtExpScriptBuilder.() -> Unit) : List<Cmd> {
            return SmtExpScriptBuilder(termBuilder = SmtExpBitVectorTermBuilder).let {
                onThisThread {
                    preLoad.forEach { l ->
                        it.cmdProcessor.process(l)
                    }
                }
                it.f()
                it.cmdList
            }
        }

        @Suppress("unused")
        fun buildIntScript(preLoad: List<Cmd> = listOf(), f: SmtExpScriptBuilder.() -> Unit) : List<Cmd> {
            return SmtExpScriptBuilder(termBuilder = SmtExpIntTermBuilder).let {
                onThisThread {
                    preLoad.forEach { l ->
                        it.cmdProcessor.process(l)
                    }
                }
                it.f()
                it.cmdList
            }
        }
    }
}
