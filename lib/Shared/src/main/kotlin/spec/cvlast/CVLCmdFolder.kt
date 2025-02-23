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

/**
 * Traverse a [CVLCmd] (via the entry point [cmd]) visiting labels ([message]), LHS ([lhs]), and
 * expressions ([cvlExp]). Each of these base cases update an accumulator of type [T].
 * Individual functions for each cmd form can be overridden to further update the accumulator (by convention the first
 * argument to all such functions) accordingly to whatever logic.
 */
abstract class CVLCmdFolder<T> {
    abstract fun cvlExp(acc: T, exp: CVLExp) : T

    open fun cmd(acc: T, cmd: CVLCmd) : T {
        return when(cmd) {
            is CVLCmd.Composite.Block -> block(acc, cmd)
            is CVLCmd.Composite.If -> conditional(acc, cmd)
            is CVLCmd.Simple.Apply -> apply(acc, cmd)
            is CVLCmd.Simple.Assert -> assert(acc, cmd)
            is CVLCmd.Simple.Satisfy -> satisfy(acc, cmd)
            is CVLCmd.Simple.AssumeCmd.Assume -> assume(acc, cmd)
            is CVLCmd.Simple.AssumeCmd.AssumeInvariant -> assumeInvariant(acc, cmd)
            is CVLCmd.Simple.Declaration -> declaration(acc, cmd)
            is CVLCmd.Simple.Definition -> definition(acc, cmd)
            is CVLCmd.Simple.Exp -> exp(acc, cmd)
            is CVLCmd.Simple.Havoc -> havoc(acc, cmd)
            is CVLCmd.Simple.Label.End -> end(acc, cmd)
            is CVLCmd.Simple.Label.Start -> start(acc, cmd)
            is CVLCmd.Simple.ResetStorage -> resetStorage(acc, cmd)
            is CVLCmd.Simple.ResetTransientStorage -> resetTransientStorage(acc, cmd)
            is CVLCmd.Simple.Return -> returnCmd(acc, cmd)
            is CVLCmd.Simple.Revert -> revert(acc, cmd)
            is CVLCmd.Simple.Nop -> nop(acc, cmd)
        }
    }

    open fun returnCmd(acc: T, cmd: CVLCmd.Simple.Return): T {
        return cmd.exps.fold(acc) { accInner, e ->
            cvlExp(accInner, e)
        }
    }

    open fun resetStorage(acc: T, cmd: CVLCmd.Simple.ResetStorage): T {
        return cvlExp(acc, cmd.exp)
    }

    open fun resetTransientStorage(acc: T, cmd: CVLCmd.Simple.ResetTransientStorage): T {
        return cvlExp(acc, cmd.exp)
    }

    open fun start(acc: T, cmd: CVLCmd.Simple.Label.Start): T {
        return message(acc, cmd.content.toString())
    }

    open fun end(acc: T, cmd: CVLCmd.Simple.Label.End): T {
        return acc
    }

    open fun havoc(acc: T, cmd: CVLCmd.Simple.Havoc): T {
        val targetsAsExp = cmd.targets.map { it.asExp }
        val foldedTargets = targetsAsExp.fold(acc, this::cvlExp)
        return cvlExp(foldedTargets, cmd.assumingExpOrDefault)
    }

    open fun exp(acc: T, cmd: CVLCmd.Simple.Exp): T {
        return cvlExp(acc, cmd.exp)
    }

    abstract fun lhs(acc: T, lhs: CVLLhs) : T
    abstract fun message(acc: T, message: String) : T

    open fun definition(acc: T, cmd: CVLCmd.Simple.Definition): T {
        return cmd.idL.fold(cvlExp(acc, cmd.exp), this::lhs)
    }

    open fun declaration(acc: T, cmd: CVLCmd.Simple.Declaration): T {
        return acc
    }

    open fun assume(acc: T, cmd: CVLCmd.Simple.AssumeCmd.Assume) : T {
        return cvlExp(acc, cmd.exp)
    }

    open fun assumeInvariant(acc: T, cmd: CVLCmd.Simple.AssumeCmd.AssumeInvariant) : T {
        return cmd.params.fold(acc, this::cvlExp)
    }

    open fun assert(acc: T, cmd: CVLCmd.Simple.Assert) : T {
        return message(cvlExp(acc, cmd.exp), cmd.description)
    }

    open fun satisfy(acc: T, cmd: CVLCmd.Simple.Satisfy) : T {
        return message(cvlExp(acc, cmd.exp), cmd.description)
    }

    open fun apply(acc: T, cmd : CVLCmd.Simple.Apply) : T {
        return cvlExp(acc, cmd.exp)
    }

    open fun conditional(acc: T, cmd: CVLCmd.Composite.If) : T {
        return cmd(
            cmd(
                cvlExp(acc, cmd.cond),
                cmd.thenCmd
            ), cmd.elseCmd
        )
    }

    open fun block(acc: T, cmd: CVLCmd.Composite.Block) : T {
        return cmd.block.fold(acc) { currAcc, it ->
            cmd(currAcc, it)
        }
    }

    open fun nop(acc: T, cmd: CVLCmd.Simple.Nop): T {
        return acc
    }

    open fun revert(acc: T, cmd: CVLCmd.Simple.Revert): T {
        return acc
    }
}
