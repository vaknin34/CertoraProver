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

package vc.summary

import smt.solverscript.LExpressionFactory
import tac.MetaMap
import vc.data.*

/**
 * Converts a TACCmd.Simple (packaged in [HasTACSimpleCmd]) to an [LExpressionWithComment] in the straightforward way.
 *
 * NB:
 * 1. This assumes TACSimpleSimple. In particular
 *     - not all statements are supported
 *     - input commands must be in passified form, i.e., DSA/SSA transformation must have been applied
 * 2. This will crash on [AssertCmd] -- the caller needs to convert those to something else or filter
 *   them out beforehand.
 * 3. Will ignore `JumpiCmds`, i.e. translate them to `True` --> if the caller wants something else, they need to
 *    convert them to `AssumeCmd`s accordingly beforehand. (a whole list of other commands is also translated to True,
 *     including havocs, revert/return, etc. those are not supposed to hold meaning at TACSimpleSimple level.
 *
 */
object TACCmdToLExpression {
    /**
     * @param hasTACSimpleCmd the [TACCmd.Simple] that is to be translated
     * @param lxf LExpressionFactory used to create the translation results
     * @param symbolTable tac symbol table, used when translating TAC to LExpressions
     * @param trackToLExpTranslation a lambda that the caller can use to track which TACExpr was translated to which
     *    LExpression (useful for backtranslation purposes, was introduced to track select terms in particular)
     */
    fun toLExpression(
        hasTACSimpleCmd: HasTACSimpleCmd,
        lxf: LExpressionFactory,
        symbolTable: TACSymbolTable,
        trackToLExpTranslation: (ToLExpression, LExpression) -> Unit,
    ): LExpressionWithComment {
        fun TACExpr.toLExp() =
            ToLExpression(
                this,
                lxf,
                symbolTable,
                hasTACSimpleCmd.getMeta()
            ) { tExp: ToLExpression, lExp: LExpression -> trackToLExpTranslation(tExp, lExp) }

        return LExpressionWithComment(lxf {
            when (val cmd = hasTACSimpleCmd.cmd) {
                is TACCmd.Simple.AssertCmd -> throw IllegalArgumentException("This method does not accept " +
                        "assertions as part of the input, only assignments and assumes (got: \"$hasTACSimpleCmd\")")
                is TACCmd.Simple.AssigningCmd.AssignExpCmd ->
                    assignEq(cmd.lhs.asSym().toLExp(), cmd.rhs.toLExp())
                is TACCmd.Simple.AssumeCmd -> cmd.cond.asSym().toLExp()
                is TACCmd.Simple.AssumeExpCmd -> cmd.cond.toLExp()
                is TACCmd.Simple.AssumeNotCmd -> TACExprFactUntyped { not(cmd.cond.asSym()) }.toLExp()
                is TACCmd.Simple.AssigningCmd.AssignHavocCmd,
                is TACCmd.Simple.RevertCmd,
                is TACCmd.Simple.ReturnCmd,
                is TACCmd.Simple.ReturnSymCmd,
                TACCmd.Simple.NopCmd,
                is TACCmd.Simple.LogCmd,
                is TACCmd.Simple.AnnotationCmd,
                is TACCmd.Simple.LabelCmd,
                is TACCmd.Simple.JumpCmd,
                is TACCmd.Simple.JumpdestCmd,
                is TACCmd.Simple.JumpiCmd -> TRUE

                else -> error("expecting TACSimpleSimple, got command \"$cmd\"")
            }
        }, hasTACSimpleCmd.getComment().toString())
    }


    /** Specifies the comment we want to add in the smt file for the corresponding command. */
    private fun HasTACSimpleCmd.getComment(): Any = this

    /** Specifies the [LExpMeta] that we attach to the [LExpression] we are creating from `this`. */
    private fun HasTACSimpleCmd.getMeta(): MetaMap? =
        when (this) {
            is TACCmd.Simple -> null
            else -> null
        }

}
