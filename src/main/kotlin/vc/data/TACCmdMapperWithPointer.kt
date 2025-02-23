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

import analysis.CmdPointer
import analysis.LTACCmd

/**
 * An extension of TACCmdMapper to see the CmdPointer.
 * Allows to implement a mapping command that is aware of the CmdPointer of the mapped command.
 *
 * Note that you must use the mapping functions provided in this interface, otherwise [currentPtr] might not be updated
 *  correctly (e.g. if you directly use something like [TACCmdMapper.mapJumpICmd]).
 **/
interface TACCmdMapperWithPointer {
    var currentPtr: CmdPointer?
    val decls : MutableSet<TACSymbol.Var>

    fun inv() = check(currentPtr != null) { "Must always set current ptr for command mapper" }

    fun mapCommand(c: LTACCmd): List<TACCmd.Simple>

    private fun updateCommandAt(p: CmdPointer, l: TACCmd.Simple): List<TACCmd.Simple> {
        currentPtr = p
        return mapCommand(LTACCmd(p, l))
    }

    fun mapCommands(c: CoreTACProgram): CoreTACProgram {
        val g = c.analysisCache.graph
        val mut = c.toPatchingProgram()
        g.commands.forEach { cmd ->
            mut.replace(cmd.ptr, this::updateCommandAt)
        }
        mut.addVarDecls(decls)
        decls.clear()
        return mut.toCode(c)
    }

    fun mapSubsetOfCommands(c: CoreTACProgram, filter: (LTACCmd) -> Boolean): CoreTACProgram {
        val g = c.analysisCache.graph
        val mut = c.toPatchingProgram()
        g.commands
            .filter(filter)
            .forEach { cmd ->
                mut.replace(cmd.ptr, this::updateCommandAt)
            }
        mut.addVarDecls(decls)
        decls.clear()
        return mut.toCode(c)
    }

    /**
     * Applies the mapping on the mutable program [mut] and on the set of commands [cmds]
     * Assumes all commands in [cmds] are valid in [mut]
     */
    fun mapSubsetOfCommandsInPlace(mut: SimplePatchingProgram, cmds: Collection<LTACCmd>) {
        cmds.forEach {
            mut.replace(it.ptr, this::updateCommandAt)
        }
        mut.addVarDecls(decls)
        decls.clear()
    }
}
