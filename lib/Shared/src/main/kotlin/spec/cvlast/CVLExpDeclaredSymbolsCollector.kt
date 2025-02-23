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

package spec.cvlast

import utils.flatMapToSet
import utils.mapToSet

object CVLExpDeclaredSymbolsCollector {
    private fun getDeclaredSymbols(exp: CVLExp): Set<Pair<String, CVLType.PureCVLType>> =
        exp.subExprsOfType<CVLExp.QuantifierExp>().mapToSet { it.qVarName to it.qVarType }

    /**
     * Returns all symbols and [CVLType]s thereof that are declared either by a [CVLCmd.Simple.Declaration] command
     * or by a [CVLCmd.Simple.Definition] command,
     * or bound by a quantifier in a [CVLExp.QuantifierExp].
     */
    fun getDeclaredSymbols(cmd: CVLCmd): Set<Pair<String, CVLType.PureCVLType>> {
        return when (cmd) {
            is CVLCmd.Simple.Declaration -> {
                setOf(Pair(cmd.id, cmd.cvlType))
            }
            is CVLCmd.Simple.Definition -> {
                if (cmd.type != null) {
                    if (cmd.idL.size != 1) {
                        throw UnsupportedOperationException("Currently, tuples in lhs cannot include a type (got $cmd)")
                    }
                    if (cmd.idL.first() !is CVLLhs.Id) {
                        throw UnsupportedOperationException(
                            "Declaring definitions cannot have an array/map access on " +
                                    "their left hand side (got $cmd)"
                        )
                    }
                    getDeclaredSymbols(cmd.exp) + Pair(cmd.idL.map { it.getIdLhs().id }.single(), cmd.type)
                } else {
                    getDeclaredSymbols(cmd.exp)
                }
            }
            is CVLCmd.Simple.Havoc -> emptySet()
            is CVLCmd.Simple.AssumeCmd.Assume -> getDeclaredSymbols(cmd.exp)
            is CVLCmd.Simple.AssumeCmd.AssumeInvariant -> emptySet()
            is CVLCmd.Composite.If -> {
                getDeclaredSymbols(cmd.cond) + getDeclaredSymbols(cmd.thenCmd) + getDeclaredSymbols(cmd.elseCmd)
            }
            is CVLCmd.Composite.Block -> {
                cmd.block.flatMap { getDeclaredSymbols(it) }.toSet()
            }
            is CVLCmd.Simple.Assert -> getDeclaredSymbols(cmd.exp)
            is CVLCmd.Simple.Satisfy -> getDeclaredSymbols(cmd.exp)
            is CVLCmd.Simple.ResetStorage -> getDeclaredSymbols(cmd.exp)
            is CVLCmd.Simple.ResetTransientStorage -> getDeclaredSymbols(cmd.exp)
            is CVLCmd.Simple.Apply -> getDeclaredSymbols(cmd.exp)
            is CVLCmd.Simple.Return -> cmd.exps.flatMapToSet { getDeclaredSymbols(it) }
            is CVLCmd.Simple.Exp -> getDeclaredSymbols(cmd.exp)
            is CVLCmd.Simple.Label -> emptySet()
            is CVLCmd.Simple.Nop -> emptySet()
            is CVLCmd.Simple.Revert -> emptySet()
        }
    }

}
