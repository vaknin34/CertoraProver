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

import log.*
import utils.monadicMap
import vc.data.TACExpr
import vc.data.TACSymbol

open class ExpressionTranslator<Repr>(
    protected val lifter: ISMTTermBuilder<*, Repr>,
    private val toTypedArray: List<Repr>.() -> Array<Repr>
) {
    open fun blastExpr(e: TACExpr, vm: (TACSymbol.Var) -> String?): Repr? {
        return when (e) {
            is TACExpr.Sym.Var -> {
                vm.invoke(e.s)?.let(lifter::toIdent)
            }
            is TACExpr.Sym.Const -> {
                try {
                    lifter.const(e.s.value)
                } catch (exception: InvalidBitVectorTerm) {
                    Logger.alwaysWarn("Failed to build term for $e", exception)
                    null
                }
            }
            is TACExpr.BinRel -> {
                when (e) {
                    is TACExpr.BinRel.Gt -> lifter::gt
                    is TACExpr.BinRel.Lt -> lifter::lt
                    is TACExpr.BinRel.Ge -> lifter::ge
                    is TACExpr.BinRel.Le -> lifter::le
                    is TACExpr.BinRel.Eq -> lifter::eq
                    is TACExpr.BinRel.Slt -> lifter::slt
                    is TACExpr.BinRel.Sle -> lifter::sle
                    is TACExpr.BinRel.Sge -> lifter::sge
                    is TACExpr.BinRel.Sgt -> lifter::sgt
                }.let { cmp ->
                    blastExpr(e.o1, vm)?.let { left ->
                        blastExpr(e.o2, vm)?.let { right ->
                            lifter.ite(
                                cmp(left, right),
                                lifter.const(1),
                                lifter.const(0)
                            )
                        }
                    }
                }
            }
            is TACExpr.Vec.Add -> {
                vecOp(e, lifter::plus, vm)
            }
            is TACExpr.Vec.Mul -> {
                vecOp(e, lifter::mult, vm)
            }
            is TACExpr.BinOp.Sub -> {
                binOp(e, lifter::minus, vm)
            }
            is TACExpr.BinOp.BWAnd -> {
                binOp(e, lifter::bwAnd, vm)
            }
            is TACExpr.BinOp.Div -> {
                binOp(e, lifter::div, vm)
            }
            is TACExpr.BinOp.BWOr -> {
                binOp(e, lifter::bwOr, vm)
            }
            is TACExpr.BinOp.ShiftLeft -> {
                binOp(e, lifter::shl, vm)
            }
            is TACExpr.BinOp.ShiftRightLogical -> {
                binOp(e, lifter::shr, vm)
            }
            is TACExpr.UnaryExp.LNot -> {
                blastExpr(e.o, vm)?.let { expr ->
                    lifter.ite(
                        lifter.eq(expr, lifter.const(0)),
                        lifter.const(1),
                        lifter.const(0)
                    )
                }
            }
            is TACExpr.UnaryExp.BWNot -> {
                blastExpr(e.o, vm)?.let(lifter::bwNot)
            }
            is TACExpr.BinBoolOp.LOr -> {
                e.ls.monadicMap {
                    blastExpr(it, vm)?.let {
                        lifter.eq(it, lifter.const(0))
                    }
                }?.let {
                    lifter.ite(
                        lifter.land(
                            *it.toTypedArray()
                        ),
                        lifter.const(0),
                        lifter.const(1)
                    )
                }
            }
            is TACExpr.BinBoolOp.LAnd -> {
                e.ls.monadicMap {
                    blastExpr(it, vm)?.let {
                        lifter.eq(it, lifter.const(0))
                    }
                }?.let { it ->
                    lifter.ite(
                        lifter.lor(
                            *it.toTypedArray()
                        ),
                        lifter.const(0),
                        lifter.const(1)
                    )
                }
            }
            is TACExpr.TernaryExp.Ite -> {
                blastExpr(e.i, vm)?.let { cond ->
                    blastExpr(e.t, vm)?.let { t ->
                        blastExpr(e.e, vm)?.let { e ->
                            lifter.ite(
                                lifter.eq(cond, lifter.const(0)),
                                e,
                                t
                            )
                        }
                    }
                }
            }
            else -> null
        }
    }

    private fun vecOp(e: TACExpr.Vec, build: (ops: List<Repr>) -> Repr, vm: (TACSymbol.Var) -> String?): Repr? {
        return e.ls.monadicMap {
            this.blastExpr(it, vm)
        }?.let {
            build(it)
        }
    }

    private fun binOp(e: TACExpr.BinOp, build: (Repr, Repr) -> Repr?, vm: (TACSymbol.Var) -> String?): Repr? {
        return blastExpr(e.o1, vm)?.let { o1 ->
            blastExpr(e.o2, vm)?.let { o2 ->
                build(o1, o2)
            }
        }
    }
}
