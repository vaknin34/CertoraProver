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

package vc.data

import tac.Tag
import java.io.Serializable
import java.math.BigInteger

interface EggTAC : Serializable {
    /**
     * Returns sexp formatted strings
     */
    override fun toString(): String

    /**
     * Convert EggTAC to TACExpr
     */
    fun toTAC(): TACExpr
}

class EggVar(val v: String, val type: Tag) : EggTAC {
    override fun toString(): String {
        return v
    }

    override fun toTAC(): TACExpr {
        return TACSymbol.Var(v, type).asSym()
    }
}

class EggConst(val c: BigInteger) : EggTAC {
    override fun toString(): String {
        return c.toString()
    }

    override fun toTAC(): TACExpr {
        return TACExpr.Sym.Const(TACSymbol.Const(c))
    }
}

class EggUnary(val op: String, val child: EggTAC) : EggTAC {
    override fun toString(): String {
        return "($op $child)"
    }

    companion object {
        val optTable: Map<String, (TACExpr) -> TACExpr> = mapOf(
            "!" to {a -> TACExpr.UnaryExp.LNot(a)},
            "~" to {a -> TACExpr.UnaryExp.BWNot(a)},
        )
    }

    override fun toTAC(): TACExpr {
        return optTable[op]?.invoke(child.toTAC()) ?: throw IllegalArgumentException("EggUnary.toTAC: Unknown unary operator: $op")
    }
}

class EggBinary(val op: String, val o1: EggTAC, val o2: EggTAC) : EggTAC {
    override fun toString(): String {
        return "($op $o1 $o2)"
    }

    companion object {
        val optTable: Map<String, (TACExpr, TACExpr) -> TACExpr> = mapOf(
            "+" to {a, b -> TACExpr.Vec.Add(a, b)},
            "*" to {a, b -> TACExpr.Vec.Mul(a, b)},

            "exp" to {a, b -> TACExpr.BinOp.Exponent(a, b)},
            "-" to {a, b -> TACExpr.BinOp.Sub(a, b)},
            "/" to {a, b -> TACExpr.BinOp.Div(a, b)},

            "&" to {a, b -> TACExpr.BinOp.BWAnd(a, b)},
            "|" to {a, b -> TACExpr.BinOp.BWOr(a, b)},
            "^" to {a, b -> TACExpr.BinOp.BWXOr(a, b)},
            "<<" to {a, b -> TACExpr.BinOp.ShiftLeft(a, b)},
            ">>" to {a, b -> TACExpr.BinOp.ShiftRightLogical(a, b)},
            ">>>" to {a, b -> TACExpr.BinOp.ShiftRightArithmetical(a, b)},

            ">" to {a, b -> TACExpr.BinRel.Gt(a, b)},
            ">=" to {a, b -> TACExpr.BinRel.Ge(a, b)},
            "<" to {a, b -> TACExpr.BinRel.Lt(a, b)},
            "<=" to {a, b -> TACExpr.BinRel.Le(a, b)},
            "==" to {a, b -> TACExpr.BinRel.Eq(a, b)},
            "s>" to {a, b -> TACExpr.BinRel.Sgt(a, b)},
            "s>=" to {a, b -> TACExpr.BinRel.Sge(a, b)},
            "s<" to {a, b -> TACExpr.BinRel.Slt(a, b)},
            "s<=" to {a, b -> TACExpr.BinRel.Sle(a, b)},

            "&&" to {a, b -> TACExpr.BinBoolOp.LAnd(a, b)},
            "||" to {a, b -> TACExpr.BinBoolOp.LOr(a, b)},
        )
    }

    override fun toTAC(): TACExpr {
        optTable[op]?.let {
            return it(o1.toTAC(), o2.toTAC())
        } ?: throw IllegalArgumentException("EggBinary.toTAC: Unknown binary operator: $op")
    }
}

object TACToEgg {
    private fun wrapEggUnary(justBitvector: Boolean, op: String, e: TACExpr): EggTAC? {
        val child = convert(e, justBitvector)
        return if (child != null) {
            EggUnary(op, child)
        } else {
            null
        }
    }


    private fun wrapEgg(justBitvector: Boolean, op: String, e1: TACExpr, e2: TACExpr): EggTAC? {
        val child1 = convert(e1, justBitvector)
        val child2 = convert(e2, justBitvector)
        return if (child1 != null && child2 != null) {
            EggBinary(op, child1, child2)
        } else {
            null
        }
    }

    private fun wrapEgg(justBitvector: Boolean, op: String, ops: List<TACExpr>) : EggTAC? {
        require(ops.size >= 2) {
            "Argument underflow"
        }
        var curr = EggBinary(
            op,
            convert(ops[0], justBitvector) ?: return null,
            convert(ops[1], justBitvector) ?: return null
        )
        var i = 2
        while(i < ops.size) {
            curr = EggBinary(
                op,
                curr,
                convert(ops[i++], justBitvector) ?: return null
            )
        }
        return curr
    }

    fun convert(tacExpr: TACExpr, justBitvector: Boolean): EggTAC? {
        return when (tacExpr) {
            is TACExpr.Sym.Var -> EggVar(tacExpr.s.namePrefix, tacExpr.s.tag)
            is TACExpr.Sym.Const -> EggConst(tacExpr.s.value)

            is TACExpr.BinOp.Sub -> wrapEgg(justBitvector, "-", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinOp.Div -> wrapEgg(justBitvector, "/", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinOp.Exponent -> wrapEgg(justBitvector, "exp", tacExpr.o1, tacExpr.o2)

            is TACExpr.BinOp.BWAnd -> wrapEgg(justBitvector, "&", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinOp.BWOr -> wrapEgg(justBitvector, "|", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinOp.ShiftLeft -> wrapEgg(justBitvector, "<<", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinOp.ShiftRightLogical -> wrapEgg(justBitvector, ">>", tacExpr.o1, tacExpr.o2)

            is TACExpr.BinBoolOp.LOr -> wrapEgg(justBitvector, "||", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinBoolOp.LAnd -> wrapEgg(justBitvector, "&&", tacExpr.o1, tacExpr.o2)

            is TACExpr.BinRel.Gt -> wrapEgg(justBitvector, ">", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinRel.Ge -> wrapEgg(justBitvector, ">=", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinRel.Lt -> wrapEgg(justBitvector, "<", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinRel.Le -> wrapEgg(justBitvector, "<=", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinRel.Eq -> wrapEgg(justBitvector, "==", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinRel.Slt -> wrapEgg(justBitvector, "s<", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinRel.Sle -> wrapEgg(justBitvector, "s<=", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinRel.Sgt -> wrapEgg(justBitvector, "s>", tacExpr.o1, tacExpr.o2)
            is TACExpr.BinRel.Sge -> wrapEgg(justBitvector, "s>=", tacExpr.o1, tacExpr.o2)

            is TACExpr.Vec.Add  -> if (tacExpr.ls.size == 1) {
                convert(tacExpr.ls[0], justBitvector)
            } else {
                wrapEgg(justBitvector, "+", tacExpr.ls)
            }

            is TACExpr.Vec.Mul -> if (tacExpr.ls.size == 1) {
                convert(tacExpr.ls[0], justBitvector)
            } else {
                wrapEgg(justBitvector, "*", tacExpr.ls)
            }

            is TACExpr.UnaryExp.LNot -> wrapEggUnary(justBitvector, "!", tacExpr.o)
            is TACExpr.UnaryExp.BWNot -> wrapEggUnary(justBitvector, "~", tacExpr.o)

            else -> if (justBitvector) {
                null
            } else {
                // placeholder for Chandra's work
                null
            }
        }

    }
}



