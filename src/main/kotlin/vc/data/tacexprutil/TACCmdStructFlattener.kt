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

import analysis.CommandWithRequiredDecls
import analysis.CommandWithRequiredDecls.Companion.withDecls
import datastructures.stdcollections.*
import tac.Tag
import utils.CertoraInternalErrorType
import utils.CertoraInternalException
import vc.data.*

/** replace all [TACExpr.StructAccess] by [TACExpr.Sym] with the according variable names. */
class TACCmdStructFlattener(val newDecls: MutableSet<TACSymbol.Var> = mutableSetOf()) : DefaultTACCmdMapper() {
    private val exprTransformer = object : DefaultTACExprTransformer() {
        override fun transform(exp: TACExpr): TACExpr =
            if (exp is TACExpr.StructAccess) {
                val s = exp.toSymbol()
                if (s is TACSymbol.Var) {
                    if (exp.struct is TACExpr.Sym.Var) {
                        val baseVar = exp.struct.s
                        s.withMetaIfNotNull(TACMeta.CVL_DEF_SITE, baseVar.meta.find(TACMeta.CVL_DEF_SITE))
                            .withMetaIfNotNull(TACMeta.CVL_VAR, baseVar.meta.find(TACMeta.CVL_VAR))
                    } else {
                        s
                    }.also { v ->
                        newDecls.addNonTransient(v)
                    }
                } else {
                    s
                }.asSym()
            } else {
                super.transform(exp)
            }
    }
    override fun mapExpr(expr: TACExpr): TACExpr = exprTransformer.transform(expr)

    companion object {
        private fun allAccesses(lhs: TACExpr, rhs: TACExpr): List<Pair<TACExpr.StructAccess, TACExpr.StructAccess>> =
                when (val tag = rhs.tagAssumeChecked) {
                    is Tag.UserDefined.Struct -> tag.fields.flatMap { field ->
                        allAccesses(TACExpr.StructAccess(lhs, field.name, field.type),
                                TACExpr.StructAccess(rhs, field.name, field.type))
                    }
                    else -> {
                        if (lhs is TACExpr.StructAccess && rhs is TACExpr.StructAccess) {
                            listOf(lhs to rhs)
                        } else {
                            throw CertoraInternalException(CertoraInternalErrorType.TAC_TRANSFORMER_EXCEPTION,
                                    "Expected lhs to be a struct access but got lhs: $lhs and rhs: $rhs")
                        }
                    }
                }

        /**
         * Takes any struct access in the rhs of an assignment and replaces it with a variable assigned to represent
         * that slot of that struct.
         *
         * NB the following assumptions:
         *  1. Struct accesses are always on the rhs (i.e. you cannot assign to a slot of a struct). This is because
         *     in CVL, structs may also only ever be on the rhs
         *  2. Struct accesses will always be down to a primitive slot (i.e. if there is a nested struct, there will
         *     not be a partial access). This is guaranteed by the CVL Compiler.
         */
        fun flattenStructs(c: TACCmd.Simple.AssigningCmd.AssignExpCmd): CommandWithRequiredDecls<TACCmd.Simple> {
            return allAccesses(c.lhs.asSym(), c.rhs).let(this::generateAssignments)
        }

        private fun generateAssignments(
            l: List<Pair<TACExpr.StructAccess, TACExpr>>
        ) : CommandWithRequiredDecls<TACCmd.Simple> {
            val localVars = mutableSetOf<TACSymbol.Var>()
            val mapper = TACCmdStructFlattener(localVars)
            // step 1: split any assignment to a struct into a series of assignments to split out variables over every
            //         nested member of that struct
            return l.map { (lhs, rhs) ->
                val assignTo = lhs.toSymbol() as TACSymbol.Var
                val flattenedLhs = if (rhs is TACExpr.StructAccess && rhs.struct is TACExpr.Sym.Var && rhs.struct.s.meta.containsKey(TACMeta.CVL_DISPLAY_NAME)) {
                    assignTo.withMeta(TACMeta.CVL_DISPLAY_NAME, rhs.struct.s.meta.find(TACMeta.CVL_DISPLAY_NAME)!!)
                } else {
                    assignTo
                }
                // we'll let step 2 handle flattening rhs so we can have the struct access -> flat variable nonsense
                // happen in one location
                localVars.addNonTransient(flattenedLhs)
                localVars.addAllNonTransient(rhs.getFreeVars())
                TACCmd.Simple.AssigningCmd.AssignExpCmd(flattenedLhs, rhs)
            }.map { cmd ->
                // step 2: flatten all struct accesses on any nested subexpression of the rhs
                mapper.map(cmd)
            }.withDecls(localVars)
        }

        fun flattenStructs(c: TACCmd.Simple.AssigningCmd.AssignHavocCmd): CommandWithRequiredDecls<TACCmd.Simple> {
            val decls = mutableSetOf<TACSymbol.Var>()
            return allAccesses(c.lhs.asSym(), c.lhs.asSym()).map { (access, _) ->
                val assignTo = access.toSymbol() as TACSymbol.Var
                decls.addNonTransient(assignTo)
                TACCmd.Simple.AssigningCmd.AssignHavocCmd(assignTo)
            }.withDecls(decls)
        }
    }
}

private fun MutableSet<TACSymbol.Var>.addNonTransient(v: TACSymbol.Var) {
    if (v.tag !is Tag.TransientTag) { this.add(v) }
}

private fun MutableSet<TACSymbol.Var>.addAllNonTransient(vars: Collection<TACSymbol.Var>) {
    vars.forEach { this.addNonTransient(it) }
}
