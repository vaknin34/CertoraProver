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

import smt.solverscript.LExpressionFactory
import smt.solverscript.functionsymbols.FunctionSymbol
import tac.MetaMap
import java.math.BigInteger

interface ToLExpression {
    class Conv(
        val lxf: LExpressionFactory,
        val symbolTable: TACSymbolTable,
        private val action: ((ToLExpression, LExpression) -> Unit)? = null,
    ) {
        /**
         * Call this on subexpressions in overrides of the [toLExpression] function.
         *
         * TODO: We should probably consolidate the meta annotations by doing .meta(meta) here. (not in this PR though)
         *   - currently it is very easy to forget to pass on the meta
         *   - it seems to be passed on in enough places for our uses (mostly understanding control flow in axiom
         *      generation)
         *   - if we want, e.g., detailed LExpMeta.ExpPointer, annotations, just doing .meta(meta) here would not
         *      suffice; we could e.g. pass the operand-index as a parameter of this method -- then we could still
         *      update meta here ...
         *   We're tracking this also in CER-1508.
         */
        operator fun invoke(toLExpression: ToLExpression, meta: MetaMap? = null): LExpression =
            toLExpression.toLExpression(this, meta).also { action?.invoke(toLExpression, it) }
    }

    /**
     * Must ONLY be called by [Conv.invoke]. (Don't know a good way to statically enforce this...)
     */
    fun toLExpression(
        conv: Conv,
        meta: MetaMap? = null,
    ): LExpression

    companion object {
        operator fun invoke(
            toLExpression: ToLExpression,
            lExprFact: LExpressionFactory,
            symbolTable: TACSymbolTable,
            meta: MetaMap? = null,
            action: (ToLExpression, LExpression) -> Unit = { _, _ -> },
        ) = Conv(lExprFact, symbolTable, action)(toLExpression, meta)

    }
}

interface BinaryToLExpression : ToLExpression {
    val smtName: FunctionSymbol
    val o1: TACExpr
    val o2: TACExpr
    override fun toLExpression(conv: ToLExpression.Conv, meta: MetaMap?): LExpression =
        conv.lxf.applyExp(
            smtName,
            conv(o1, meta),
            conv(o2, meta),
            meta = meta
        )
}

interface VecToLExpression : ToLExpression {
    val smtName: FunctionSymbol
    val ls: List<TACExpr>

    /**
     * Returns the corresponding [LExpression] in case [ls.isEmpty()].
     */
    fun toLExpressionAsNullary(conv: ToLExpression.Conv, meta: MetaMap?): LExpression

    /**
     * Returns the corresponding [LExpression] in case [ls.size == 1].
     */
    fun toLExpressionAsUnary(
        conv: ToLExpression.Conv,
        meta: MetaMap?
    ): LExpression =
        conv(ls.first(), meta)

    /**
     * Returns the corresponding [LExpression] in case [ls.size > 1].
     */
    fun toLExpressionAsNAry(conv: ToLExpression.Conv, meta: MetaMap?): LExpression =
        conv.lxf.applyExp(smtName, ls.map { conv(it, meta) }, meta)


    override fun toLExpression(conv: ToLExpression.Conv, meta: MetaMap?): LExpression =
        when (ls.size) {
            0 -> toLExpressionAsNullary(conv, meta)
            1 -> toLExpressionAsUnary(conv, meta)
            else -> toLExpressionAsNAry(conv, meta)
        }

}

interface VecToLExpressionWithInitValue<T> : VecToLExpression {
    val initValue: T

    // Needed to work around a compiler bug.  Without these we get NoSuchMethodError.
    override fun toLExpressionAsUnary(conv: ToLExpression.Conv, meta: MetaMap? ): LExpression = super.toLExpressionAsUnary(conv, meta)
    override fun toLExpressionAsNAry(conv: ToLExpression.Conv, meta: MetaMap?): LExpression = super.toLExpressionAsNAry(conv, meta)
    override fun toLExpression(conv: ToLExpression.Conv, meta: MetaMap?): LExpression = super.toLExpression(conv, meta)
}

interface VecToLExpressionWithInitBigInt : VecToLExpressionWithInitValue<BigInteger> {
    override fun toLExpressionAsNullary(conv: ToLExpression.Conv, meta: MetaMap?): LExpression =
        conv.lxf.litInt(initValue)

    // Needed to work around a compiler bug.  Without these we get NoSuchMethodError.
    override fun toLExpressionAsUnary(conv: ToLExpression.Conv, meta: MetaMap?): LExpression =
        super.toLExpressionAsUnary(conv, meta)

    override fun toLExpressionAsNAry(conv: ToLExpression.Conv, meta: MetaMap?): LExpression =
        super.toLExpressionAsNAry(conv, meta)

    override fun toLExpression(conv: ToLExpression.Conv, meta: MetaMap?): LExpression = super.toLExpression(conv, meta)
}

interface VecToLExpressionWithInitBool : VecToLExpressionWithInitValue<Boolean> {
    override fun toLExpressionAsNullary(conv: ToLExpression.Conv, meta: MetaMap?): LExpression =
        conv.lxf.litBool(initValue)

    // Needed to work around a compiler bug.  Without these we get NoSuchMethodError.
    override fun toLExpressionAsUnary(conv: ToLExpression.Conv, meta: MetaMap?): LExpression =
        super.toLExpressionAsUnary(conv, meta)

    override fun toLExpressionAsNAry(conv: ToLExpression.Conv, meta: MetaMap?): LExpression =
        super.toLExpressionAsNAry(conv, meta)

    override fun toLExpression(conv: ToLExpression.Conv, meta: MetaMap?): LExpression = super.toLExpression(conv, meta)
}

interface VecToLExpressionByBinOp : VecToLExpressionWithInitBigInt {

    fun binOp(
        conv: ToLExpression.Conv,
        ACC: LExpression,
        o: TACExpr,
        meta: MetaMap?
    ): LExpression =
        conv.lxf.applyExp(smtName, ACC, conv(o, meta), meta = meta)

    override fun toLExpressionAsNAry(conv: ToLExpression.Conv, meta: MetaMap?): LExpression =
        ls.drop(1).fold(conv(ls.first(), meta)) { ACC, o ->
            binOp(conv, ACC, o, meta)
        }

    // Needed to work around a compiler bug.  Without these we get NoSuchMethodError.
    override fun toLExpressionAsUnary(conv: ToLExpression.Conv, meta: MetaMap? ): LExpression = super.toLExpressionAsUnary(conv, meta)
    override fun toLExpression(conv: ToLExpression.Conv, meta: MetaMap?): LExpression = super.toLExpression(conv, meta)
}

interface UnaryToLExpression : ToLExpression {
    val smtName: FunctionSymbol
    val o: TACExpr
    override fun toLExpression(conv: ToLExpression.Conv, meta: MetaMap?): LExpression =
        conv.lxf.applyExp(smtName, conv(o, meta), meta = meta)
}
