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

package vc.data.parser

import tac.MetaMap
import vc.data.*

/**
 * Helper class for the TAC.cup parser
 */
object TACCmdParserUtils {


    fun getNthArg(cmdName: String, args: List<CmdArguments>, ind: Int, expected: Int): CmdArguments {
        if (ind < args.size && ind >= 0) {
            return args[ind]
        } else {
            throw IllegalArgumentException("TAC Command " + cmdName + " expects " + expected + " but was only given " + args.size)
        }
    }

    fun throwCastingException(expected: String, cmdArg: CmdArguments): Nothing =
        throw IllegalArgumentException(
            "Illegal parsing, expected $expected value but got ${cmdArg::class}"
        )

    inline fun <reified T : Enum<T>> getValueEnum(cmdArg: CmdArguments) : T {
        return java.lang.Enum.valueOf(T::class.java, getValueString(cmdArg))

    }

    fun getValueString(cmdArg: CmdArguments) =
        (cmdArg as? CmdArguments.TACString)?.str ?: throwCastingException("TACString", cmdArg)

    fun getValueExpr(cmdArg: CmdArguments) =
        (cmdArg as? CmdArguments.TACExprArg)?.exp ?: throwCastingException("TACExprArg", cmdArg)

    fun getValueSymbol(cmdArg: CmdArguments) =
        (getValueExpr(cmdArg) as? TACExpr.Sym)?.s ?: throwCastingException("TACExpr.Sym", cmdArg)

    fun getValueVar(cmdArg: CmdArguments) =
        getValueSymbol(cmdArg) as? TACSymbol.Var ?: throwCastingException("TACSymbol.Var", cmdArg)

    fun getValueBlock(cmdArg: CmdArguments) =
        (cmdArg as? CmdArguments.BlockID)?.blockIds ?: throwCastingException("BlockId", cmdArg)

    fun resolveMetaReference(id: Int?, mapOfMetaMap: Map<Int,MetaMap>): tac.MetaMap = id?.let{mapOfMetaMap[it]!!} ?: MetaMap()

}
class MetaRefToMetaMapper(private val metaRefs: Map<Int, MetaMap>) : DefaultTACCmdMapper() {
    override fun mapVar(t: TACSymbol.Var): TACSymbol.Var = t.withResolvedMetaRefs(metaRefs)
}

fun TACSymbol.Var.withResolvedMetaRefs(metaRefs: Map<Int, MetaMap>): TACSymbol.Var {
    if (meta.containsKey(META_REF_INDEX)) {
        val i = meta.get<Int>(META_REF_INDEX)
        return withMeta { _ -> metaRefs[i]!! }
    }
    return this
}
