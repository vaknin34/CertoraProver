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

package vc.data.parser;

import tac.MetaKey
import tac.MetaMap
import utils.uncheckedAs
import vc.data.*
import vc.data.parser.TACCmdParserUtils.getValueEnum
import vc.data.parser.TACCmdParserUtils.getValueString
import vc.data.parser.TACCmdParserUtils.getValueSymbol
import vc.data.parser.TACCmdParserUtils.getValueVar
import java.io.Serializable


class TACCmdParserImplementation(symbolTable: TACSymbolTable, mapOfMetaMap: Map<Int,MetaMap>) : AbstractTACParserCmd(symbolTable, mapOfMetaMap) {

    override fun parseAssignSimpleSha3Cmd(
        args: List<CmdArguments>,
        meta: MetaMap) =

        TACCmd.Simple.AssigningCmd.AssignSimpleSha3Cmd(
            getValueVar(args[0]),
            getValueSymbol(args[1]) as TACSymbol.Const,
            args.drop(2).map { TACCmdParserUtils.getValueSymbol(it) },
            meta
        )


    override fun parseLogCmd(args: List<CmdArguments>, meta: MetaMap) =
        TACCmd.Simple.LogCmd(
            args.dropLast(1).map {  TACCmdParserUtils.getValueSymbol(it) },
            getValueVar(args.get(args.size -1)),
            meta
        )


    override fun parseSummaryCmd(args: List<CmdArguments>, meta: MetaMap): TACCmd.Simple.SummaryCmd {
        val tacSummary : TACSummary = inlinedTACJson.decodeFromString(getValueString(args[0]))
        return TACCmd.Simple.SummaryCmd(tacSummary, meta)
    }

    override fun parseAnnotationCmd(args: List<CmdArguments>, meta: MetaMap): TACCmd.Simple.AnnotationCmd {
        val entry = inlinedTACJson.decodeFromString(MetaMap.EntrySerializationSurrogate.serializer(), getValueString(args[0]))
        return TACCmd.Simple.AnnotationCmd(
            @Suppress("Treapability")
            TACCmd.Simple.AnnotationCmd.Annotation(entry.key.uncheckedAs<MetaKey<Serializable>>(), entry.value),
            meta)
    }

    override fun parseCallCore(args: List<CmdArguments>, meta: MetaMap) = TACCmd.Simple.CallCore(
        getValueSymbol(args[0]),
        getValueSymbol(args[1]),
        getValueSymbol(args[2]),
        getValueSymbol(args[3]),
        getValueVar(args[4]),
        getValueSymbol(args[5]),
        getValueSymbol(args[6]),
        getValueVar(args[7]),
        getValueEnum<TACCallType>(args[8]),
        getValueSymbol(args[9]),
        meta)

    override fun parseRevertCmd(args: List<CmdArguments>, meta: MetaMap): TACCmd.Simple.RevertCmd {
        return TACCmd.Simple.RevertCmd(getValueSymbol(args[0]),
            getValueSymbol(args[1]),
            getValueEnum<TACRevertType>(args[2]),
            getValueVar(args[3]),
            meta)
    }
}

