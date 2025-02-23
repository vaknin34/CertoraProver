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

package parser

import annotations.PollutesGlobalState
import config.CommandLineParser
import config.Config
import config.DefaultCommandLineParser
import config.realOpt
import log.*
import org.junit.jupiter.api.*
import utils.logging.captureLogs

class JavaArgsParserTest {

    class JavaParsingException(msg: String): Exception(msg)

    private val harnessedCommandLineParser = object: DefaultCommandLineParser() {
        override fun printMsgAndExit(
            msg: String?,
            withHelp: Boolean,
            allHelp: Boolean,
            withVersion: Boolean,
            exitcode: Int
        ): Nothing {
            throw JavaParsingException(msg?:"")
        }

        fun _noSuchOptionErrStr(opt: String) = super.noSuchOptionErrStr(opt)
    }

    @PollutesGlobalState
    private fun basicParsing(args: Array<String>) {
        harnessedCommandLineParser.processArgsAndConfig(args)
    }

    @PollutesGlobalState
    private fun checkParsingException(args: Array<String>, expectedMessage: String) {
        assertThrows<JavaParsingException> { basicParsing(args) }.let {
            Assertions.assertEquals(expectedMessage, it.message)
        }
    }

    @Test
    @Disabled // Pollutes global config; do not run in CI!
    @PollutesGlobalState
    fun testDups() {
        val badOption = "-bNOTEXISTING"
        val badOptionMessage = harnessedCommandLineParser.withAddendum(harnessedCommandLineParser._noSuchOptionErrStr(badOption))

        val goodOption = "-b"

        checkParsingException(arrayOf(goodOption, "2", badOption), badOptionMessage)
        checkParsingException(arrayOf(goodOption, "2", badOption, "10"), badOptionMessage)
        checkParsingException(arrayOf(goodOption, "2", badOption, "str"), badOptionMessage)
        checkParsingException(arrayOf(badOption,"10", goodOption,"2"), badOptionMessage)
        checkParsingException(arrayOf(badOption, goodOption,"2"), badOptionMessage)

        val invalidOptionMsg = harnessedCommandLineParser.withAddendum("Invalid option $badOption")
        checkParsingException(arrayOf(badOption,"str", goodOption,"2"), badOptionMessage)
        checkParsingException(arrayOf(badOption), invalidOptionMsg)
        checkParsingException(arrayOf(badOption,"10"), invalidOptionMsg)
        checkParsingException(arrayOf(badOption,"str"), invalidOptionMsg)

        val badValueForGoodOption = harnessedCommandLineParser.withAddendum("Missing argument for option: b")
        checkParsingException(arrayOf(goodOption, badOption), badValueForGoodOption)
        checkParsingException(arrayOf(goodOption, badOption, "10"), badValueForGoodOption)
        checkParsingException(arrayOf(goodOption, badOption, "str"), badValueForGoodOption)

        // sanity
        assertDoesNotThrow { basicParsing(arrayOf(goodOption, "2")) }
    }

    @Test
    @Disabled // Pollutes global config; do not run in CI!
    @PollutesGlobalState
    fun testMultipleAliases() {
        val option = Config.Smt.UseNIA
        check(option.aliases.isNotEmpty()) { "This unit test requires an option with aliases" }
        val alias1 = option.option
        val alias2 = option.aliases.first()
        val (out, _) = captureLogs {
            basicParsing(arrayOf("-${alias1.realOpt()}", "true", "-${alias2.realOpt()}", "false"))
        }
        Assertions.assertEquals(
            "Warning: Option ${option.name} was set using multiple aliases (-${alias1.opt}, -${alias2.opt}), will use -${alias1.opt}. Please use only a single one.",
            out
        )
    }

    companion object {
        @JvmStatic
        @BeforeAll
        fun setup() {
            CommandLineParser.registerConfigurations()
        }
    }
}
