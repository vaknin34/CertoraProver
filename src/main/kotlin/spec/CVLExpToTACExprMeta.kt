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

package spec

import com.certora.collect.*
import datastructures.stdcollections.*
import spec.cvlast.CVLExp
import spec.cvlast.CVLType
import utils.*
import vc.data.TACSymbol
import vc.data.TransformableSymEntityWithRlxSupport
import java.io.Serializable

/**
 * Stores meta information about compiled CVL expressions, including their concrete syntax ([expLabel]) and their
 * type [expType].
 *
 * Basically a wrapper-AST for [CVLExp] that, in addition to the expression stores the [TACSymbol]s, as well as some
 * extra info (like [CVLType]) for each sub-expression.
 * We attach this as TAC meta to the CVL compilation outputs in [CVLExpressionCompiler].
 * Q (alex n, thinking aloud): Do we really need to do that? Wouldn't it be enough to have these ASTs in the SnippetCmds
 * that we'll print ultimatively?
 *  --> we'd have to pick them up in CVL land rather than here, then (?)
 */
@KSerializable
sealed class CVLExpToTACExprMeta : TransformableSymEntityWithRlxSupport<CVLExpToTACExprMeta>, AmbiSerializable {
    abstract val exp: CVLExp
    val expLabel: String
        get() = exp.toString()
    val expType: CVLType
        get() = exp.getCVLType()

    abstract fun getOperands(): List<Operand>

    /**
     * Compiled Nullary CVL expression.
     */
    @KSerializable
    data class NullaryCVLExp(override val exp: CVLExp) : CVLExpToTACExprMeta() {

        override fun getOperands(): List<Operand> = emptyList()
        override fun transformSymbols(f: (TACSymbol) -> TACSymbol): CVLExpToTACExprMeta {
            return this
        }
    }

    /**
     * Stores information about an CVL Expression.
     * [out]: the smt value of the expression.
     * [label]: string representation of the expression.
     * [isCVLVariableExp]: for [NullaryCVLExp] (Terminal expression), whether it is a variable (eg. a).
     * [isCVLConstExp]: for [NullaryCVLExp] (Terminal expression), whether it is a constant (eg. 5).
     * [typ]: the variable type.
     */
    @KSerializable
    @Treapable
    data class Operand(
        val out: TACSymbol,
        val exp: CVLExp,
    ) : Serializable {
        val label: String
            get() = exp.toString()
        val isCVLVariableExp: Boolean
            get() = exp is CVLExp.VariableExp
        val isCVLConstExp: Boolean
            get() = exp is CVLExp.Constant || exp.getCVLTypeOrNull() is CVLType.PureCVLType.Primitive.NumberLiteral
        val typ: CVLType
            get() = exp.getCVLType()
    }

    /**
     * Compiled binary CVL expression. [o1] and [o2] are the out-symbols of its two subexpressions.
     */
    @KSerializable
    data class BinaryCVLExp(override val exp: CVLExp, val o1: Operand, val o2: Operand) : CVLExpToTACExprMeta() {
        constructor(
            exp: CVLExp,
            o1Out: TACSymbol,
            o1Exp: CVLExp,
            o2Out: TACSymbol,
            o2Exp: CVLExp
        ) : this(exp, Operand(o1Out, o1Exp), Operand(o2Out, o2Exp))

        override fun getOperands(): List<Operand> = listOf(o1, o2)
        override fun transformSymbols(f: (TACSymbol) -> TACSymbol): CVLExpToTACExprMeta {
            return copy(
                o1 = o1.copy(out = f(o1.out)),
                o2 = o2.copy(out = f(o2.out))
            )
        }
    }

    /**
     * Compiled unary CVL expression. [o] is the out-symbol of its only subexpression.
     */
    @KSerializable
    data class UnaryCVLExp(override val exp: CVLExp, val o: Operand) : CVLExpToTACExprMeta() {
        constructor(exp: CVLExp, oOut: TACSymbol, oExp: CVLExp) : this(exp, Operand(oOut, oExp))

        override fun getOperands(): List<Operand> = listOf(o)
        override fun transformSymbols(f: (TACSymbol) -> TACSymbol): CVLExpToTACExprMeta {
            return copy(
                o = o.copy(out = f(o.out))
            )
        }
    }

    /**
     * Compiled ternary CVL expression. [o1], [o2], and [o3] are the out-symbols of its three subexpressions.
     */
    @KSerializable
    data class TernaryCVLExp(override val exp: CVLExp, val o1: Operand, val o2: Operand, val o3: Operand) : CVLExpToTACExprMeta() {
        constructor(
            exp: CVLExp,
            o1Out: TACSymbol,
            o1Exp: CVLExp,
            o2Out: TACSymbol,
            o2Exp: CVLExp,
            o3Out: TACSymbol,
            o3Exp: CVLExp,
        ) : this(exp, Operand(o1Out, o1Exp), Operand(o2Out, o2Exp), Operand(o3Out, o3Exp))

        override fun getOperands(): List<Operand> = listOf(o1, o2, o3)
        override fun transformSymbols(f: (TACSymbol) -> TACSymbol): CVLExpToTACExprMeta {
            return copy(
                o1 = o1.copy(out = f(o1.out)),
                o2 = o2.copy(out = f(o2.out)),
                o3 = o3.copy(out = f(o3.out))
            )
        }
    }
}
