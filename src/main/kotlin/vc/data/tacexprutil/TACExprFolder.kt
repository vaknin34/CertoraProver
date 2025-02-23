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

package vc.data.tacexprutil

import com.certora.collect.*
import datastructures.stdcollections.*
import tac.MetaKey
import tac.MetaMap
import utils.uncheckedAs
import vc.data.TACBuiltInFunction
import vc.data.TACExpr
import vc.data.TACSymbol
import vc.data.WithSupport
import java.io.Serializable

/**
 * Note that unless overridden, this will recurse into the `mentionedVariables` of both [MetaMap]s attached to
 * variables, and those of [TACExpr.AnnotationExp]. This behavior is different than that of [TACExprTransformer]
 * and it's default implementations.
 */
abstract class TACExprFolder<T> {
    open fun expr(acc: T, v: TACExpr) : T {
        return when(v) {
            is TACExpr.Sym -> this.sym(acc, v)
            is TACExpr.Vec -> this.vec(acc, v)
            is TACExpr.SimpleHash -> this.simplehash(acc, v)
            is TACExpr.TernaryExp.Ite -> this.ite(acc, v)
            is TACExpr.TernaryExp.MulMod -> this.mulMod(acc, v)
            is TACExpr.TernaryExp.AddMod -> this.addMod(acc, v)
            is TACExpr.UnaryExp -> this.unaryExp(acc, v)
            is TACExpr.BinOp -> this.binOp(acc, v)
            is TACExpr.BinRel -> this.binRel(acc, v)
            is TACExpr.Apply -> this.apply(acc, v)
            is TACExpr.Select -> this.select(acc, v)
            is TACExpr.MapDefinition -> this.mapDefinition(acc, v)
            is TACExpr.Unconstrained -> this.unconstrained(acc)
            is TACExpr.Store -> this.store(acc, v)
            is TACExpr.MultiDimStore -> this.multidimstore(acc, v)
            is TACExpr.LongStore -> this.longStore(acc, v)
            is TACExpr.BinBoolOp -> this.binBoolOp(acc, v)
            is TACExpr.QuantifiedFormula -> this.quantifiedFormula(acc, v)
            is TACExpr.StructAccess -> this.structAccess(acc, v)
            is TACExpr.StructConstant -> this.structConstant(acc, v)
            is TACExpr.AnnotationExp<*> -> this.annotationExp(acc, v)
        }
    }

    open fun structConstant(acc: T, v: TACExpr.StructConstant): T {
        return v.fieldNameToValue.entries.fold(acc) { Curr, (k, v) ->
            this.expr(this.string(Curr, k), v)
        }
    }

    open fun structAccess(acc: T, v: TACExpr.StructAccess): T {
        return this.string(acc, v.fieldName).let { a ->
            this.expr(a, v.struct)
        }
    }

    open fun sym(acc: T, v: TACExpr.Sym): T {
        return when(v) {
            is TACExpr.Sym.Var -> this.varSym(acc, v)
            is TACExpr.Sym.Const -> this.constSym(acc, v)
        }
    }

    @Suppress("Treapability")
    open fun meta(acc: T, m: MetaMap): T =
        m.map.entries.fold(acc) { current, pair ->
            metaPair(current, pair.key.uncheckedAs(), pair.value)
        }

    open fun <@Treapable R : Serializable> annotationExp(acc : T, a : TACExpr.AnnotationExp<R>) : T =
        this.expr(metaPair(acc, a.annot.k, a.annot.v), a.o)

    open fun <@Treapable R : Serializable> metaPair(acc : T, k : MetaKey<R>, v : R) =
        if (v is WithSupport) {
            foldSubExpr(acc, *(v.support.map { it.asSym()}).toTypedArray())
        } else {
            acc
        }

    open fun constSym(acc: T, v: TACExpr.Sym.Const): T {
        return const(acc, v.s)
    }

    open fun varSym(acc: T, v: TACExpr.Sym.Var): T {
        return variable(meta(acc, v.s.meta), v.s)
    }

    abstract fun const(acc: T, v: TACSymbol.Const): T

    abstract fun variable(acc: T, v: TACSymbol.Var) : T

    private fun foldSubExpr(acc: T, vararg e: TACExpr) : T = e.fold(acc) { curr, it ->
        this.expr(curr, it)
    }

    open fun mapDefinition(acc: T, e: TACExpr.MapDefinition): T =
        foldSubExpr(acc, *(e.defParams + listOf(e.definition)).toTypedArray())

    open fun unconstrained(acc: T): T = acc

    open fun binBoolOp(acc: T, v: TACExpr.BinBoolOp): T {
        return when(v) {
            is TACExpr.BinBoolOp.LAnd -> this.land(acc, v)
            is TACExpr.BinBoolOp.LOr -> this.lor(acc, v)
        }
    }

    open fun string(acc: T, v: String) = acc

    open fun binRel(acc: T, v: TACExpr.BinRel): T {
        return when(v) {
            is TACExpr.BinRel.Gt -> this.gt(acc, v)
            is TACExpr.BinRel.Lt -> this.lt(acc, v)
            is TACExpr.BinRel.Ge -> this.ge(acc, v)
            is TACExpr.BinRel.Le -> this.le(acc, v)
            is TACExpr.BinRel.Eq -> this.eq(acc, v)
            is TACExpr.BinRel.Slt -> this.slt(acc, v)
            is TACExpr.BinRel.Sle -> this.sle(acc, v)
            is TACExpr.BinRel.Sge -> this.sge(acc, v)
            is TACExpr.BinRel.Sgt -> this.sgt(acc, v)
        }
    }

    open fun binOp(acc: T, v: TACExpr.BinOp): T {
        return when(v) {
            is TACExpr.BinOp.IntSub -> this.intsub(acc, v)
            is TACExpr.BinOp.Sub -> this.sub(acc, v)
            is TACExpr.BinOp.Div -> this.div(acc, v)
            is TACExpr.BinOp.SDiv -> this.sdiv(acc, v)
            is TACExpr.BinOp.IntDiv -> this.intdiv(acc, v)
            is TACExpr.BinOp.Mod -> this.mod(acc, v)
            is TACExpr.BinOp.SMod -> this.smod(acc, v)
            is TACExpr.BinOp.IntMod -> this.intmod(acc, v)
            is TACExpr.BinOp.Exponent -> this.exponent(acc, v)
            is TACExpr.BinOp.IntExponent -> this.intexponent(acc, v)
            is TACExpr.BinOp.BWAnd -> this.bwand(acc, v)
            is TACExpr.BinOp.BWOr -> this.bwor(acc, v)
            is TACExpr.BinOp.BWXOr -> this.bwxor(acc, v)
            is TACExpr.BinOp.ShiftLeft -> this.shiftleft(acc, v)
            is TACExpr.BinOp.ShiftRightLogical -> this.shiftrightlogical(acc, v)
            is TACExpr.BinOp.ShiftRightArithmetical -> this.shiftrightarithmetical(acc, v)
            is TACExpr.BinOp.SignExtend -> this.signextend(acc, v)
        }
    }

    open fun signextend(acc: T, v: TACExpr.BinOp.SignExtend): T = this.expr(this.expr(acc, v.o1), v.o2)

    open fun unaryExp(acc: T, v: TACExpr.UnaryExp): T {
        return when(v) {
            is TACExpr.UnaryExp.BWNot -> this.bwnot(acc, v)
            is TACExpr.UnaryExp.LNot -> this.lnot(acc, v)
        }
    }

    open fun vec(acc: T, v: TACExpr.Vec): T {
        return when(v) {
            is TACExpr.Vec.Mul -> this.mul(acc, v)
            is TACExpr.Vec.IntMul -> this.intmul(acc, v)
            is TACExpr.Vec.IntAdd -> this.intadd(acc, v)
            is TACExpr.Vec.Add -> this.add(acc, v)
        }
    }

    open fun mul(acc: T, v: TACExpr.Vec.Mul): T = foldSubExpr(acc, *v.ls.toTypedArray())
    open fun intmul(acc: T, v: TACExpr.Vec.IntMul): T = foldSubExpr(acc, *v.ls.toTypedArray())
    open fun intadd(acc: T, v: TACExpr.Vec.IntAdd): T = foldSubExpr(acc, *v.ls.toTypedArray())
    open fun add(acc: T, v: TACExpr.Vec.Add): T = foldSubExpr(acc, *v.ls.toTypedArray())
    open fun simplehash(acc: T, v: TACExpr.SimpleHash): T = foldSubExpr(acc, *(listOf(v.length) + v.args).toTypedArray())


    open fun le(acc: T, v: TACExpr.BinRel.Le): T = foldSubExpr(acc, v.o1, v.o2)
    open fun ge(acc: T, v: TACExpr.BinRel.Ge): T = foldSubExpr(acc, v.o1, v.o2)
    open fun lt(acc: T, v: TACExpr.BinRel.Lt): T = foldSubExpr(acc, v.o1, v.o2)
    open fun slt(acc: T, v: TACExpr.BinRel.Slt): T = foldSubExpr(acc, v.o1, v.o2)
    open fun sle(acc: T, v: TACExpr.BinRel.Sle): T = foldSubExpr(acc, v.o1, v.o2)
    open fun sgt(acc: T, v: TACExpr.BinRel.Sgt): T = foldSubExpr(acc, v.o1, v.o2)
    open fun sge(acc: T, v: TACExpr.BinRel.Sge): T = foldSubExpr(acc, v.o1, v.o2)
    open fun eq(acc: T, v: TACExpr.BinRel.Eq): T = foldSubExpr(acc, v.o1, v.o2)
    open fun gt(acc: T, v: TACExpr.BinRel.Gt): T = foldSubExpr(acc, v.o1, v.o2)

    open fun intsub(acc: T, v: TACExpr.BinOp.IntSub): T = foldSubExpr(acc, v.o1, v.o2)
    open fun sub(acc: T, v: TACExpr.BinOp.Sub): T = foldSubExpr(acc, v.o1, v.o2)
    open fun div(acc: T, v: TACExpr.BinOp.Div): T = foldSubExpr(acc, v.o1, v.o2)
    open fun sdiv(acc: T, v: TACExpr.BinOp.SDiv): T = foldSubExpr(acc, v.o1, v.o2)
    open fun intdiv(acc: T, v: TACExpr.BinOp.IntDiv): T = foldSubExpr(acc, v.o1, v.o2)
    open fun mod(acc: T, v: TACExpr.BinOp.Mod): T = foldSubExpr(acc, v.o1, v.o2)
    open fun smod(acc: T, v: TACExpr.BinOp.SMod): T = foldSubExpr(acc, v.o1, v.o2)
    open fun intmod(acc: T, v: TACExpr.BinOp.IntMod): T = foldSubExpr(acc, v.o1, v.o2)
    open fun exponent(acc: T, v: TACExpr.BinOp.Exponent): T = foldSubExpr(acc, v.o1, v.o2)
    open fun intexponent(acc: T, v: TACExpr.BinOp.IntExponent): T = foldSubExpr(acc, v.o1, v.o2)
    open fun bwand(acc: T, v: TACExpr.BinOp.BWAnd): T = foldSubExpr(acc, v.o1, v.o2)
    open fun bwor(acc: T, v: TACExpr.BinOp.BWOr): T = foldSubExpr(acc, v.o1, v.o2)
    open fun bwxor(acc: T, v: TACExpr.BinOp.BWXOr): T = foldSubExpr(acc, v.o1, v.o2)
    open fun shiftleft(acc: T, v: TACExpr.BinOp.ShiftLeft): T = foldSubExpr(acc, v.o1, v.o2)
    open fun shiftrightlogical(acc: T, v: TACExpr.BinOp.ShiftRightLogical): T = foldSubExpr(acc, v.o1, v.o2)
    open fun shiftrightarithmetical(acc: T, v: TACExpr.BinOp.ShiftRightArithmetical): T = foldSubExpr(acc, v.o1, v.o2)

    open fun bwnot(acc: T, v: TACExpr.UnaryExp.BWNot): T = this.expr(acc, v.o)
    open fun lnot(acc: T, v: TACExpr.UnaryExp.LNot): T = this.expr(acc, v.o)

    open fun lor(acc: T, v: TACExpr.BinBoolOp.LOr): T = foldSubExpr(acc, *v.ls.toTypedArray())
    open fun land(acc: T, v: TACExpr.BinBoolOp.LAnd): T = foldSubExpr(acc, *v.ls.toTypedArray())

    open fun select(acc: T, v: TACExpr.Select): T = foldSubExpr(acc, v.base, v.loc)
    open fun ite(acc: T, v: TACExpr.TernaryExp.Ite): T = this.foldSubExpr(acc, v.i, v.t, v.e)
    open fun mulMod(acc: T, v: TACExpr.TernaryExp.MulMod): T = this.foldSubExpr(acc, v.a, v.b, v.n)
    open fun addMod(acc: T, v: TACExpr.TernaryExp.AddMod): T = this.foldSubExpr(acc, v.a, v.b, v.n)
    open fun quantifiedFormula(acc: T, v: TACExpr.QuantifiedFormula): T = this.foldSubExpr(acc, v.body)

    open fun longStore(acc: T, v: TACExpr.LongStore): T =
            foldSubExpr(acc, v.dstMap, v.dstOffset, v.length, v.srcMap, v.srcOffset)

    open fun store(acc: T, v: TACExpr.Store): T = foldSubExpr(acc, v.base, v.loc, v.value)
    open fun multidimstore(acc: T, v: TACExpr.MultiDimStore): T =
        foldSubExpr(acc, *(listOf(v.base) + v.locs + listOf(v.value)).toTypedArray())

    open fun functionsym(acc: T, f: TACExpr.TACFunctionSym) : T = when(f) {
        is TACExpr.TACFunctionSym.BuiltIn -> bif(acc, f.bif)
        is TACExpr.TACFunctionSym.Adhoc -> string(acc, f.name)
    }

    open fun bif(acc: T, bif: TACBuiltInFunction): T = acc

    open fun apply(acc: T, v: TACExpr.Apply) : T {
        return functionsym(acc, v.f).let {
            v.ops.fold(it, this::expr)
        }
    }
}
