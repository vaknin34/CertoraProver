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

package wasm.tacutils

import analysis.*
import analysis.CommandWithRequiredDecls.Companion.mergeMany
import analysis.CommandWithRequiredDecls.Companion.withDecls
import datastructures.stdcollections.*
import instrumentation.transformers.*
import kotlin.streams.*
import tac.*
import utils.*
import vc.data.*
import vc.data.tacexprutil.*
import wasm.host.soroban.opt.LONG_COPY_STRIDE

fun assignHavoc(dest: TACSymbol.Var) =
    listOf(TACCmd.Simple.AssigningCmd.AssignHavocCmd(dest)).withDecls(dest)

fun assign(dest: TACSymbol.Var, exp: TACExprFact.() -> TACExpr) =
    ExprUnfolder.unfoldTo(TACExprFactUntyped(exp), dest).merge(dest)

/** Helper for logical implication */
infix fun TACExpr.implies(other: TACExpr): TACExpr =
    TACExprFactUntyped { not(this@implies) or other }

fun TACExpr.letVar(
    name: String,
    tag: Tag = Tag.Bit256,
    f: (TACExpr.Sym.Var) -> CommandWithRequiredDecls<TACCmd.Simple>
) = TACKeyword.TMP(tag, name).let { v ->
    mergeMany(
        assign(v) { this@TACExpr },
        f(v.asSym())
    )
}

fun memStore(l: TACExpr, v: TACExpr) =
    l.letVar { ls ->
        v.letVar { vs ->
            TACCmd.Simple.AssigningCmd.ByteStore(ls.s, vs.s, TACKeyword.MEMORY.toVar())
                .withDecls(TACKeyword.MEMORY.toVar())
        }
    }

fun TACExpr.letVar(
    tag: Tag = Tag.Bit256,
    f: (TACExpr.Sym.Var) -> CommandWithRequiredDecls<TACCmd.Simple>
) = letVar("", tag, f)

fun (TACExprFact.() -> TACExpr).letVar(
    name: String = "",
    tag: Tag = Tag.Bit256,
    f: (TACExpr.Sym.Var) -> CommandWithRequiredDecls<TACCmd.Simple>
) = TACExprFactUntyped.this().letVar(name, tag, f)

fun TACCmd.Simple.withDecls(vararg decls: TACSymbol.Var) = listOf(this).withDecls(*decls)

fun assert(msg: String, subjectSym: TACSymbol? = null, cond: TACExprFact.() -> TACExpr) =
    cond.letVar("a", Tag.Bool) {
        val meta = subjectSym?.let { MetaMap(TACCmd.Simple.AssertCmd.FORMAT_ARG1 to it) } ?: MetaMap()
        TACCmd.Simple.AssertCmd(it.s, msg, meta).withDecls()
    }

fun assume(cond: TACExprFact.() -> TACExpr) =
    cond.letVar("a", Tag.Bool) {
        TACCmd.Simple.AssumeCmd(it.s).withDecls()
    }

fun label(label: String) = TACCmd.Simple.LabelCmd(label).withDecls()

fun defineMap(
    map: TACSymbol.Var,
    def: TACExprFact.(List<TACExpr.Sym.Var>) -> TACExpr
): CommandWithRequiredDecls<TACCmd.Simple> {
    val mapType = map.tag as Tag.Map
    val queryVars = mapType.paramSorts.map { TACKeyword.TMP(it) }
    val queryParams = queryVars.map { it.asSym() }

    return assign(map) {
        MapDefinition(
            queryParams,
            def(queryParams),
            mapType
        )
    }
}

/** Copies from a ByteMap into a temporary map, and calls [f] with the temporary map var. */
fun letBuf(
    fromByteMap: TACSymbol.Var,
    fromPos: TACExprFact.() -> TACExpr,
    len: TACExprFact.() -> TACExpr,
    stride: Int,
    f: (TACExpr.Sym.Var) -> CommandWithRequiredDecls<TACCmd.Simple>
) = fromPos.letVar { pos ->
    len.letVar { len ->
        TACKeyword.TMP(Tag.ByteMap).let { toByteMap ->
            mergeMany(
                listOf(
                    TACCmd.Simple.ByteLongCopy(
                        srcBase = fromByteMap,
                        srcOffset = pos.s,
                        dstBase = toByteMap,
                        dstOffset = TACSymbol.Zero,
                        length = len.s,
                        meta = MetaMap(LONG_COPY_STRIDE to stride)
                    )
                ).withDecls(toByteMap),
                f(toByteMap.asSym())
            )
        }
    }
}
