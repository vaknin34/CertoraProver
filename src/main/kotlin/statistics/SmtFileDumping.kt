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

@file:Suppress("unused") // CER-1486

package statistics

import config.OUTPUT_NAME_DELIMITER
import log.*
import smtlibutils.cmdprocessor.CmdProcessor
import smtlibutils.cmdprocessor.PrintingFormulaChecker
import smtlibutils.cmdprocessor.SmtFormulaCheckerQuery
import smtlibutils.cmdprocessor.SmtFormulaCheckerResult
import smtlibutils.data.FactorySmtScript
import utils.ArtifactFileUtils
import vc.data.CoreTACProgram
import vc.data.parser.serializeTAC


private val logger = Logger(LoggerTypes.TIMEOUT_REPORTING)


object SmtFileDumping {

    /**
     * Dump the given formula and program if present.
     * Note that we give them the same name (besides file type suffix), so if both are given, they should also
     * belong together in some sense.
     *
     * The dumped files' names will always start with [fileNamePrefix].
     *
     * Takes care of naming by
     *  - using the [fileNamePrefix]
     *  - using the smt querie's name, or the tac program's name, or a default, in that order as part of the name
     *  - making the name unique
     * */
    suspend fun dumpFormulaAndOrProgram(
        fileNamePrefix: String,
        smtFormulaCheckerResult: SmtFormulaCheckerResult?,
        ctp: CoreTACProgram?
    ) {
        // see if we have a smt query that we can get a nice name from (typically including split info and such)
        val repSingle = smtFormulaCheckerResult?.getRepresentativeSingle()
        val sampleQuery: SmtFormulaCheckerQuery? = repSingle?.query

        // the part of the name that says which particular query we're looking at
        val specificName = sampleQuery?.info?.name ?: ctp?.name ?: "defaultDumpName"

        val dumpFileBaseName = "${fileNamePrefix}_" +
            ArtifactFileUtils.getBasenameOnly(ArtifactManagerFactory().getFilePathForSmtQuery(specificName, subdir = null))

        sampleQuery?.let { dumpSmt(it, dumpFileBaseName) }
        ctp?.let { dumpTacProgram(it, dumpFileBaseName) }
    }

    /**
     * Dump the formula in the given query to the given file.
     * The file will automatically be dumped in the `formulas` directory and `.smt2` will be appended to the name.
     *
     * Note that the user is responsible for unique naming here; this method does not make names unique on its own.
     */
    suspend fun dumpSmt(smtQuery: SmtFormulaCheckerQuery, dumpFileBaseName: String) {
        val smtDumpFileName = "$dumpFileBaseName.smt2"
        ArtifactManagerFactory().registerArtifact(smtDumpFileName, StaticArtifactLocation.Formulas) { fileName ->
            // write the smt file
            PrintingFormulaChecker.printer(
                FactorySmtScript,
                fileName,
                CmdProcessor.Options.fromQuery(smtQuery, false)
            ).check(smtQuery)
        }
    }

    private fun SmtFormulaCheckerResult.getRepresentativeSingle(): SmtFormulaCheckerResult.Single =
        when (this) {
            is SmtFormulaCheckerResult.Single -> this
            is SmtFormulaCheckerResult.Agg -> this.representativeResult
        }

    /**
     * Dump the given tac program to the given file.
     * The file will automatically be dumped in the `outputs` directory and `.tac` will be appended to the name.
     *
     * Note that the user is responsible for unique naming here; this method does not make names unique on its own.
     */
    fun dumpTacProgram(
        ctp: CoreTACProgram,
        dumpFileBaseName: String,
    ) {
        val dumpFileName = "$dumpFileBaseName.tac"

        ArtifactManagerFactory().registerArtifact(dumpFileName, StaticArtifactLocation.Outputs) { fileName ->
            serializeTAC(ctp, fileName)
        }
    }

    fun dumpUnsatCoresStatsFile(ruleName: String, json: String) {
        val fileName = "UnsatCoresStats$OUTPUT_NAME_DELIMITER$ruleName.json"
        ArtifactManagerFactory().registerArtifact(fileName, StaticArtifactLocation.Reports) { name ->
            ArtifactFileUtils.getWriterForFile(name, true).use { it.append(json) }
        }
    }
}
