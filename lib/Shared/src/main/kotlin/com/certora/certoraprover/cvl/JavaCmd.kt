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

package com.certora.certoraprover.cvl

import report.calltrace.CVLReportLabel
import spec.TypeResolver
import spec.cvlast.*
import spec.cvlast.CVLCmd.Simple.AssumeCmd.AssumeInvariant
import spec.cvlast.CVLScope.Item.BranchCmdScopeItem.IfCmdElseScopeItem
import spec.cvlast.CVLScope.Item.BranchCmdScopeItem.IfCmdThenScopeItem
import spec.cvlast.typechecker.CVLError
import utils.CollectingResult.Companion.flatten
import utils.CollectingResult.Companion.lift
import utils.CollectingResult.Companion.map
import utils.ErrorCollector.Companion.collectingErrors
import spec.cvlast.CVLExp.HavocTarget
import utils.*
import utils.CollectingResult.Companion.bind
import utils.CollectingResult.Companion.transpose

// This file contains the "Java" AST nodes for commands.  See README.md for a description of the Java AST.

sealed class Cmd(val cvlRange: CVLRange) : Kotlinizable<CVLCmd>

class ApplyCmd(cvlRange: CVLRange, private val applyExp: UnresolvedApplyExp) : Cmd(cvlRange) {
    override fun kotlinize(resolver: TypeResolver, scope: CVLScope): CollectingResult<CVLCmd, CVLError>
        = applyExp.kotlinize(resolver, scope).map { CVLCmd.Simple.Apply(cvlRange, it, scope) }
}

class AssertCmd(cvlRange: CVLRange, val exp: Exp, val description: String?) : Cmd(cvlRange) {
    override fun toString() = "Assert($exp,$description)"

    override fun kotlinize(resolver: TypeResolver, scope: CVLScope): CollectingResult<CVLCmd, CVLError>
        = exp
            .kotlinize(resolver, scope)
            .map { asserted ->
                val description = this.description ?: defaultAssertDescription(asserted)

                CVLCmd.Simple.Assert(cvlRange, asserted, description, scope, invariantPostCond = false)
            }
}


class AssumeCmd(_cvlRange: CVLRange, val exp: Exp) : Cmd(_cvlRange) {
    override fun toString() = "Assume($exp)"

    override fun kotlinize(resolver: TypeResolver, scope: CVLScope): CollectingResult<CVLCmd, CVLError>
        = exp.kotlinize(resolver, scope).map {CVLCmd.Simple.AssumeCmd.Assume(cvlRange,it,scope,invariantPreCond = false) }
}


class AssumeInvariantCmd(_cvlRange: CVLRange, val id: String, val params: List<Exp>) : Cmd(_cvlRange) {
    override fun toString() = "AssumeInvariant($id,$params)"

    override fun kotlinize(resolver: TypeResolver, scope: CVLScope): CollectingResult<CVLCmd, CVLError>
        = params.map { it.kotlinize(resolver, scope) }.flatten().map { AssumeInvariant(cvlRange, id, it, scope) }
}


class BlockCmd(_cvlRange: CVLRange, val block: List<Cmd>) : Cmd(_cvlRange) {
    override fun toString() = "Block($block)"

    override fun kotlinize(resolver: TypeResolver, scope: CVLScope): CollectingResult<CVLCmd.Composite.Block, CVLError>
        = scope.extendInCollecting(CVLScope.Item::BlockCmdScopeItem) { newScope: CVLScope ->
            block.map { it.kotlinize(resolver, newScope) }.flatten().map { CVLCmd.Composite.Block(cvlRange,it,newScope) }
        }
}


class DeclarationCmd(val type: TypeOrLhs, val id: String, idRange: CVLRange) : Cmd(idRange) {
    override fun toString() = "Declaration($type $id)"

    override fun kotlinize(resolver: TypeResolver, scope: CVLScope): CollectingResult<CVLCmd, CVLError>
        = type.toCVLType(resolver, scope).map { CVLCmd.Simple.Declaration(cvlRange, it, id, scope) }
}


class DefinitionCmd(_cvlRange: CVLRange, val type: TypeOrLhs?, val lhs: List<TypeOrLhs>, val exp: Exp) : Cmd(_cvlRange) {
    override fun toString() = "Definition(${type?.let { "$it " }.orEmpty()}${lhs.joinToString()} := $exp)"

    override fun kotlinize(resolver: TypeResolver, scope: CVLScope): CollectingResult<CVLCmd, CVLError> = collectingErrors {
        val type = type?.toCVLType(resolver, scope) ?: null.lift()
        val lhs_ = lhs.map { it.kotlinize(resolver, scope) }.flatten()
        return@collectingErrors map(lhs_, exp.kotlinize(resolver, scope), type) { lhs, exp, resolvedType ->
            CVLCmd.Simple.Definition(cvlRange, resolvedType, lhs, exp, scope)
        }
    }
}

class HavocCmd(cvlRange: CVLRange, val targets: List<Exp>, private val assumingExp: Exp?) : Cmd(cvlRange) {
    constructor(cvlRange: CVLRange, targets: List<Exp>) : this(cvlRange, targets, null)

    override fun kotlinize(resolver: TypeResolver, scope: CVLScope): CollectingResult<CVLCmd, CVLError> = collectingErrors {
        fun kotlinizeToHavocTarget(exp: Exp) = exp.kotlinize(resolver, scope).bind(HavocTarget::fromExp)

        val targets = targets.map(::kotlinizeToHavocTarget).flatten()
        val assumingExp = assumingExp?.kotlinize(resolver, scope).transpose()

        map(targets, assumingExp) { kotlinizedTargets, kotlinizedAssumingExp ->
            CVLCmd.Simple.Havoc(cvlRange, kotlinizedTargets, kotlinizedAssumingExp, scope)
        }
    }
}


class IfCmd(cvlRange: CVLRange, val cond: Exp, val thenCmd: Cmd, val elseCmd: Cmd?) : Cmd(cvlRange) {
    override fun toString() = "If($cond,$thenCmd,${elseCmd ?: ""})"

    override fun kotlinize(resolver: TypeResolver, scope: CVLScope): CollectingResult<CVLCmd, CVLError> {
        return scope.extendInCollecting(::IfCmdThenScopeItem, ::IfCmdElseScopeItem) { th: CVLScope, els: CVLScope ->
            collectingErrors {
                val cond_    = cond.kotlinize(resolver, scope)
                val thenCmd_ = thenCmd.kotlinize(resolver, th)
                val elseCmd_ = elseCmd?.kotlinize(resolver, els) ?: CVLCmd.Simple.Nop(cvlRange, scope).lift()
                map(cond_, thenCmd_, elseCmd_) { cond, thenCmd, elseCmd ->
                    CVLCmd.Composite.If(cvlRange, cond, thenCmd, elseCmd, scope)
                }
            }
        }
    }
}


class ResetStorageCmd(_cvlRange: CVLRange, val target: Exp) : Cmd(_cvlRange) {
    override fun toString() = "reset_storage($target)"

    override fun kotlinize(resolver: TypeResolver, scope: CVLScope): CollectingResult<CVLCmd, CVLError>
        = target.kotlinize(resolver, scope).map { CVLCmd.Simple.ResetStorage(cvlRange, it, scope) }
}


class ReturnCmd(_cvlRange: CVLRange, val exps: List<Exp>) : Cmd(_cvlRange) {
    override fun toString() = "Return($exps)"

    override fun kotlinize(resolver: TypeResolver, scope: CVLScope): CollectingResult<CVLCmd, CVLError>
        = exps.map { it.kotlinize(resolver,scope) }.flatten().map { CVLCmd.Simple.Return(cvlRange, it, scope) }
}


class RevertCmd(_cvlRange: CVLRange, val reason: String?) : Cmd(_cvlRange) {
    override fun toString() = "Revert($reason)"

    override fun kotlinize(resolver: TypeResolver, scope: CVLScope): CollectingResult<CVLCmd, CVLError>
        = CVLCmd.Simple.Revert(cvlRange, reason, scope).lift()
}


class SatisfyCmd(cvlRange: CVLRange, val exp: Exp, val description: String?) : Cmd(cvlRange) {
    override fun toString() = "Satisfy($exp,$description)"

    override fun kotlinize(resolver: TypeResolver, scope: CVLScope): CollectingResult<CVLCmd, CVLError>
        = exp
            .kotlinize(resolver, scope)
            .map { asserted ->
                val description = this.description ?: defaultAssertDescription(asserted)

                CVLCmd.Simple.Satisfy(cvlRange, asserted, description, scope, invariantPostCond = false)
            }
}

/** we do this here to ensure [CVLCmd.Simple.Assert] and [CVLCmd.Simple.Satisfy] have non-null descriptions */
private fun defaultAssertDescription(asserted: CVLExp) = CVLReportLabel.Exp(asserted).toString()
