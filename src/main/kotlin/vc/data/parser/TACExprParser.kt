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


import datastructures.stdcollections.*
import tac.MetaMap
import tac.Tag
import utils.*
import vc.data.TACExpr
import vc.data.TACExprFactUntyped
import vc.data.TACSymbol


const val jsonPrefixInCmd = "JSON"
const val jsonPrefixInExp = "##"


fun parseExprFunction(str: String, args: List<TACExpr>): TACExpr =
    with(TACExprFactUntyped) {
        when (str) {
            //"Sym" -> TACExprFactUntyped.Sym(args[0]))
            //var args
            "Mul" -> Mul(args)
            "IntMul" -> IntMul(args)
            "IntAdd" -> IntAdd(args)
            "Add" -> Add(args)
            //2 args
            "IntSub" -> IntSub(args[0], args[1])
            "IntDiv" -> IntDiv(args[0], args[1])
            "IntMod" -> IntMod(args[0], args[1])
            "Mod" -> Mod(args[0], args[1])
            "SMod" -> SMod(args[0], args[1])
            "Sub" -> Sub(args[0], args[1])
            "Div" -> Div(args[0], args[1])
            "SDiv" -> SDiv(args[0], args[1])
            "Ite" -> Ite(args[0], args[1], args[2])
            "Eq" -> Eq(args[0], args[1])
            "Le" -> Le(args[0], args[1])
            "Sle" -> Sle(args[0], args[1])
            "Slt" -> Slt(args[0], args[1])
            "Lt" -> Lt(args[0], args[1])
            "Ge" -> Ge(args[0], args[1])
            "Sge" -> Sge(args[0], args[1])
            "Gt" -> Gt(args[0], args[1])
            "Sgt" -> Sgt(args[0], args[1])
            "BWAnd" -> BWAnd(args[0], args[1])
            "BWOr" -> BWOr(args[0], args[1])
            "BWNot" -> BWNot(args[0])
            "Exponent" -> Exponent(args[0], args[1])
            "IntExponent" -> IntExponent(args[0], args[1])
            "ShiftLeft" -> ShiftLeft(args[0], args[1])
            "ShiftRightLogical" -> ShiftRightLogical(args[0], args[1])
            "ShiftRightArithmetical" -> ShiftRightArithmetical(args[0], args[1])
            "BWXOr" -> TACExpr.BinOp.BWXOr(args[0], args[1])
            "Select" -> Select(args[0], args[1])
            "Store" -> Store(args[0], args[1], v = args[2])
            "LongStore" -> LongStore(args[0], args[1], args[2], args[3], args[4])
            "MultiDimStore" -> {
                val locs = args.subList(1, args.size - 1)
                Store(args[0], locs, args[args.size - 1])
            }

            "AddMod" -> AddMod(args[0], args[1], args[2])
            "MulMod" -> MulMod(args[0], args[1], args[2])
            "SignExtend" -> SignExtend(args[0], args[1])
            "LAnd" -> LAnd(args)
            "LOr" -> LOr(args)
            "LNot" -> LNot(args[0])
            //SimpleHash, Apply, ForAll, Exists, Unconstrained handled in TAC.cup
            //StructAccess,StructConstant aren't being used in CoreTAC
            else -> {
                throw IllegalArgumentException("TAC Parser: Unknown function name: $str")
            }
        }
    }

fun varListToExpr(l: List<TACSymbol.Var>) = l.map{ TACExpr.Sym.Var(it) }
fun exprAsVar(expr: TACExpr) = expr as? TACExpr.Sym.Var ?: throw IllegalArgumentException("Illegal expr type $expr")

private val primitiveTypes: Map<String, Tag> by lazy {
    mapOf(
        *((8..512 step 8).map { "bv${it}" to Tag.Bits(it) }.toTypedArray()),
        "bool" to Tag.Bool,
        "bytemap" to Tag.ByteMap,
        "wordmap" to Tag.WordMap,
        "int" to Tag.Int,
        "rawarray" to Tag.CVLArray.RawArray,
    )
}

fun getPrimitive(tagStr: String) =
    primitiveTypes[tagStr] ?: throw IllegalArgumentException("illegal or non primitive tag type: $tagStr")

fun parseAnnotationExpr(e : TACExpr, json : String) : TACExpr {
    val entry = inlinedTACJson.decodeFromString(MetaMap.EntrySerializationSurrogate.serializer(), json)
    @Suppress("Treapability")
    return TACExpr.AnnotationExp(e, entry.key.uncheckedAs(), entry.value)
}
