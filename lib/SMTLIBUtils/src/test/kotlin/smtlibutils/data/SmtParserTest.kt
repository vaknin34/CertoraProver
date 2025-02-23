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

package smtlibutils.data

import kotlinx.coroutines.flow.flowOf
import kotlinx.coroutines.runBlocking
import loaders.WithResourceFile
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.opentest4j.AssertionFailedError
import smtlibutils.cmdprocessor.CmdProcessor
import smtlibutils.cmdprocessor.ExtraCommandsCmdProcessor
import smtlibutils.cmdprocessor.SolverInstanceInfo
import smtlibutils.cmdprocessor.process
import smtlibutils.parser.SMTParser

internal class SmtParserTest : WithResourceFile {

    @Test
    fun parseScript01() {
        val parser = SMTParser(loadResourceFileOrCrash("smtparsing/parseMe01.smt2"))
        parser.parse()
        val smtScript = parser.getSmtScript()
        assertTrue((smtScript as SmtScript).symbolTable.hasFunDecl("c"))
        assertTrue(smtScript.symbolTable.hasFunDecl("d"))
        assertTrue(smtScript.symbolTable.hasFunDecl("f"))
    }

    @Test
    fun parseScript02() {
        val parser =
            SMTParser(loadResourceFileOrCrash("theorypurifier/theorySeparation01.smt2"))
        parser.parse()
        val smt = parser.getSmt()
        assertTrue(smt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == null })
        val sortedSmt = smt.sort()
        assertTrue(sortedSmt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == Sort.BoolSort })
    }

    @Test
    fun parseScript03() {
        val parser = SMTParser(loadResourceFileOrCrash("smtparsing/ITE01.smt2"))
        parser.parse()
        val smt = parser.getSmt()
        assertTrue(smt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == null })
        val sortedSmt = smt.sort()
        assertTrue(sortedSmt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == Sort.BoolSort })
    }

    @Test
    fun parseScript04() {
        val parser =
            SMTParser(loadResourceFileOrCrash("smtparsing/produceModelsTrue01.smt2"))
        parser.parse()
        val smt = parser.getSmt()
        assertTrue(smt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == null })
        val sortedSmt = smt.sort()
        assertTrue(sortedSmt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == Sort.BoolSort })
    }


    @Test
    fun parseScriptUF01() {
        val parser =
            SMTParser(loadResourceFileOrCrash("theorypurifier/theorySeparation02UF.smt2"))
        parser.parse()
        val smt = parser.getSmt()
        assertTrue(smt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == null })
        val sortedSmt = smt.sort()
        assertTrue(sortedSmt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == Sort.BoolSort })
    }

    ///////////////// datatypes

    @Test
    fun parseScriptDT01() {
        val parser =
            SMTParser(loadResourceFileOrCrash("smtparsing/dt_hash_01.smt2"))
        parser.parse()
        val smt = parser.getSmt()
        assertTrue(smt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == null })

        val smtScript = SmtScript()
        val sortedSmt = smt.sort(smtScript)
        assertTrue(sortedSmt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == Sort.BoolSort })

        assertTrue(smtScript.symbolTable.hasSortDecl("hash"))
        val hashSort =
            smtScript.symbolTable.lookUpSort("hash")?.sort ?: throw AssertionFailedError("sort not found")

        assertTrue(smtScript.symbolTable.hasFunDecl("symbol"))
        assertTrue(smtScript.symbolTable.lookUpFunction("symbol")?.param_sorts?.size == 1)
        assertTrue(smtScript.symbolTable.lookUpFunction("symbol")?.param_sorts?.first() == Sort.IntSort)
        assertTrue(smtScript.symbolTable.lookUpFunction("symbol")?.res_sort == hashSort)

        assertTrue(smtScript.symbolTable.hasFunDecl("hash"))
        assertTrue(smtScript.symbolTable.lookUpFunction("hash")?.param_sorts?.size == 2)
        assertTrue(smtScript.symbolTable.lookUpFunction("hash")?.param_sorts?.get(0) == hashSort)
        assertTrue(smtScript.symbolTable.lookUpFunction("hash")?.param_sorts?.get(1) == Sort.IntSort)
        assertTrue(smtScript.symbolTable.lookUpFunction("hash")?.res_sort == hashSort)

        assertTrue(smtScript.symbolTable.hasFunDecl("value"))
        assertTrue(smtScript.symbolTable.lookUpFunction("value")?.param_sorts?.size == 1)
        assertTrue(smtScript.symbolTable.lookUpFunction("value")?.param_sorts?.get(0) == hashSort)
        assertTrue(smtScript.symbolTable.lookUpFunction("value")?.res_sort == Sort.IntSort)
    }

    @Test
    fun parseScriptDT02() {
        val input = """
            (declare-datatypes ((Color 0))
                (((Red) (Black))))
        """.trimIndent()

        val parser = SMTParser(input)
        parser.parse()
        val smt = parser.getSmt()
        assertTrue(smt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == null })

        val smtScript = SmtScript()
        val sortedSmt = smt.sort(smtScript)
        assertTrue(sortedSmt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == Sort.BoolSort })
        assertTrue(smtScript.symbolTable.hasSortDecl("Color"))
        assertTrue(smtScript.symbolTable.hasFunDecl("Red"))
        assertTrue(smtScript.symbolTable.hasFunDecl("Black"))
    }

    @Test
    fun parseScriptDT03() {
        val input = """
            (declare-datatypes ((list 0) (tree 0))
                (((cons (head tree) (tail list)) (nil))
                 ((node (data Int) (children list)))))
        """.trimIndent()
        val parser = SMTParser(input)
        parser.parse()
        val smt = parser.getSmt()
        assertTrue(smt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == null })
        val sortedSmt = smt.sort()
        assertTrue(sortedSmt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == Sort.BoolSort })
    }

    /**
     * example taken from http://cvc4.cs.stanford.edu/wiki/Datatypes
     */
    @Test
    fun parseScriptDT04() {
        val parser =
            SMTParser(loadResourceFileOrCrash("smtparsing/dt_cvc4_list.smt2"))
        parser.parse()
        val smt = parser.getSmt()
        assertTrue(smt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == null })

        val smtScript = SmtScript()
        val sortedSmt = smt.sort(smtScript)
        assertTrue(sortedSmt.cmds.filterIsInstance<Cmd.Assert>().all { it.e.sort == Sort.BoolSort })

        assertTrue(smtScript.symbolTable.hasSortDecl("list"))
        smtScript.symbolTable.lookUpSort("list")?.sort ?: throw AssertionFailedError("sort not found")
    }

    ///////////////// commments

    @Test
    fun parseComments01() {
        val parser = SMTParser(loadResourceFileOrCrash("smtparsing/parseComments01.smt2"))
        parser.parse()
        val smt = parser.getSmt()
        assertTrue(smt.cmds.size == 6)
    }

    @Test
    fun parseComments02() {
        val parser = SMTParser(loadResourceFileOrCrash("smtparsing/parseComments02.smt2"))
        parser.parse()
        val smt = parser.getSmt()
        assertTrue(smt.cmds.size == 6)
    }

    @Test
    fun parseComments03() {
        val parser = SMTParser(loadResourceFileOrCrash("smtparsing/parseComments03.smt2"))
        parser.parse()
        assertTrue(true)
        val smt = parser.getSmt()
        assertTrue(smt.cmds.size == 1)
    }

    ///////////////// models

    @Test
    fun parseModel01() {
        val parser =
            SMTParser(loadResourceFileOrCrash("modelparsing/z3model01.txt"))
        parser.parse()
        val smt = parser.getSmt()
        assertTrue(smt.cmds.size == 1)
        assertTrue(smt.cmds[0] is Cmd.Model)
    }

    @Test
    fun parseModelCvc4_01() {
        val parser = SMTParser(
            loadResourceFileOrCrash("modelparsing/cvc4modelAUFNIA01.txt")
        )
        parser.parse()
        parser.getSmt()
        parser.getSmtScript()
    }

    @Test
    fun parseValues01() {
        try {
            SMTParser.parseValues(
                loadResourceFileOrCrash("valdefparsing/basicSoundnessTestsArrayTheory.txt"),
                FactorySmtScript
            )
//            assertTrue(parsed.size == 34)
            assertTrue(true)
        } catch (e: SMTParser.SmtParserException) {
            assertTrue(false) // is there a better way to mark something an error location?
        }
    }

    @Test
    fun parseValuesWithSymbolTable() {
        val st = SmtSymbolTable()
        val sc = SmtScript(st)

        SMTParser.parseValues("((true true) ((_ bv0 8) #b00000000))", sc)
        SMTParser.parseValues("(((= (_ bv0 8) #b00000000) true))", sc)
    }

    @Test
    fun parseValuesWithLets() {
        val st = SmtSymbolTable()
        val sc = SmtScript(st)

        st.registerDeclDatatypes(
            Cmd.DeclareDatatypes(
                listOf(SortDec("skey", 0)),
                listOf(
                    listOf(
                        DatatypeConstructorDec("basic", listOf(
                            SortedVar("simple_hash_3_sel_3", Sort.IntSort)
                        )),
                        DatatypeConstructorDec("simple_hash_3", listOf(
                            SortedVar("simple_hash_3_sel_0", Sort.SKeySort),
                            SortedVar("simple_hash_3_sel_1", Sort.SKeySort),
                            SortedVar("simple_hash_3_sel_2", Sort.SKeySort),
                            SortedVar("simple_hash_3_sel_3", Sort.IntSort)
                        )),
                    )
                )
            ), sc
        )
        st.registerDeclFun(Identifier.Simple("R490"), listOf(), Sort.SKeySort)

        val s = "((R490 (let ((a!1 (simple_hash_3\n" +
                "  (simple_hash_3 (basic 535) (basic 534) (basic 533) 7886)\n" +
                "  (simple_hash_3 (basic 535) (basic 534) (basic 533) 7886)\n" +
                "  (simple_hash_3 (basic 535) (basic 534) (basic 533) 7886)\n" +
                "  598))) (simple_hash_3 a!1 a!1 a!1 600)\n" +
                ")))"
        val res = SMTParser.parseValues(s, sc)
        assertTrue(res.size == 1)
    }

    @Test
    fun parseModelBv01() {
        val parser =
            SMTParser(loadResourceFileOrCrash("modelparsing/z3modelBv01.txt"))
        parser.parse()
        val smt = parser.getSmt()
        assertTrue(smt.cmds.size == 2)
        assertTrue(smt.cmds[0] is Cmd.Model)
        assertTrue(smt.cmds[1] is Cmd.StatsCmd)
    }

    /////////////////// push/pop

    @Test
    fun parseIncremental01() {
        val script = SharingSmtScript()
        val parser = SMTParser(loadResourceFile("smtparsing/pushPopReset01.smt2") ?: error("could not read resource"))
        parser.parse(script)
        val smt = parser.getSmt()

        val expected = listOf(
            "sat", "unsat", "sat", "sat", "unsat", "sat", "sat", "unsat", "sat"
        ).map { runBlocking { SatResult.fromCheckSatOutput(flowOf(it), SolverInstanceInfo.None) } }
        var ctr = 0

        val solver = runBlocking {
            ExtraCommandsCmdProcessor.fromCommand(
                "z3",
                listOf("z3", "-in"),
                CmdProcessor.Options.Default.copy(logic = Logic.fromString("AUFNIA")),
                debugOutput = true
            )
        }

        smt.cmds.forEach {
            if (it is Cmd.CheckSat) {
                val res = runBlocking { SatResult.fromCheckSatOutput(solver.checkSat(), SolverInstanceInfo.None) }
                assertEquals(expected[ctr], res)
                ctr++
            }
            runBlocking {
                solver.process(it)
            }
        }
        assertTrue(true)
    }

    ///////////////// value definitions (i.e. what is returned by get-value command )

    @Test
    fun parseValDefs02() {
        val script = SmtScript()
        // the script needs to be filled with the declarations from the original smt file to understand the identifiers
        // in the goal
        val parserDecl = SMTParser(loadResourceFileOrCrash("valdefparsing/ufDefinitions.smt2"))
        parserDecl.parse(script)


        val parser = SMTParser(loadResourceFileOrCrash("valdefparsing/cvc5UfModel.txt"))
        parser.parse(script)
        val smt = parser.getSmt()
        assertTrue(smt.cmds.size == 1)
        assertTrue(smt.cmds[0] is Cmd.ValDefList)
    }
}

// some aux definitions

private val intMul = SmtIntpFunctionSymbol.IRA.Mul(Sort.IntSort)
private val intDiv = SmtIntpFunctionSymbol.Ints.Div

private val mulAndDivAfss = listOf(
    SmtUnintpFunctionSymbol(
        FactorySmtScript.simpleIdentifier("absDiv"),
        intDiv.rank
    ),
    SmtUnintpFunctionSymbol(
        FactorySmtScript.simpleIdentifier("absMul"),
        intMul.rank
    ),
)

