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

package instrumentation.transformers

import datastructures.MutableReversibleMap
import datastructures.stdcollections.*
import log.*
import tac.NBId
import vc.data.*

private val logger = Logger(LoggerTypes.UNUSED_ASSIGNMENTS_OPT)

/**
 * Does per block optimizations:
 *   1. removes loop assignments `x : = x`
 *   2. inlines simple assignments `b := a; c := b + 1` => `b := a; c := a + 1`.
 *
 * If [isInlineable] of a variable is false, it is never replaced, and never replaces other variables.
 */
class AssignmentInliner(
    private val code: CoreTACProgram,
    private val isInlineable: (TACSymbol.Var) -> Boolean
) {
    private val g = code.analysisCache.graph
    private val patcher = code.toPatchingProgram()

    private fun simpleRhsOrNull(cmd: TACCmd.Simple): TACSymbol? =
        ((cmd as? TACCmd.Simple.AssigningCmd.AssignExpCmd)?.rhs as? TACExpr.Sym)?.s

    private var countReplacements = 0
    private var countRemovals = 0

    /**
     * Goes forward in the block, updating which replacements are possible, and rewriting commands with them
     * as we go.
     */
    private fun processBlock(b: NBId) {

        /** `a := b` => `canBeReplacedWith.get(a) = b`  */
        val canBeReplacedWith = MutableReversibleMap<TACSymbol.Var, TACSymbol>()

        /** follow the replacements to the root to get the oldest replacement, which is our preference */
        fun oldestReplacement(v: TACSymbol): TACSymbol =
            canBeReplacedWith[v]?.let(::oldestReplacement) ?: v

        /** Can [v] be replaced by [u] */
        fun canBeReplacedWith(v: TACSymbol, u: TACSymbol): Boolean =
            v == u || canBeReplacedWith[v]?.let { canBeReplacedWith(it, u) } == true

        /**
         * When [v] gets a new assignment, we first remove it from the graph, (later we may add it back in with its
         * new roles). However, its children can still be replaced by [v]'s parent, i.e., in:
         *    b := a
         *    c := b
         *    b := ...
         *    x := c + 1
         * Although the last `c` can't be replaced by `b`, it can still be replaced by `a`.
         */
        fun remove(v: TACSymbol.Var) {
            val parent = canBeReplacedWith.remove(v)
            for (u in canBeReplacedWith.keysOf(v).toList()) {
                parent
                    ?.let { canBeReplacedWith[u] = it }
                    ?: canBeReplacedWith.remove(u)
            }
        }

        val mapper = object : DefaultTACCmdMapper() {
            override fun mapSymbol(t: TACSymbol) = oldestReplacement(t).also {
                if (logger.isInfoEnabled && t != it) {
                    countReplacements++
                }
            }
        }

        for ((ptr, cmd) in g.elab(b).commands) {
            val lhs = cmd.getLhs()
            val rhsSym = simpleRhsOrNull(cmd)

            // For `a := b`, if `b` can be replaced by `a`, then we can remove this line.
            if (rhsSym != null && canBeReplacedWith(rhsSym, lhs!!)) {
                patcher.delete(ptr)
                countRemovals++
                // we don't register this in the graph so that it doesn't have cycles (and it can't help us anyway).
                continue
            }

            // why only these I don't know...
            if (cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd ||
                cmd is TACCmd.Simple.AssigningCmd.ByteLoad ||
                cmd is TACCmd.Simple.AssigningCmd.ByteStore
            ) {
                patcher.update(ptr, mapper.map(cmd))
            }

            if (lhs != null) {
                remove(lhs)
                if (rhsSym != null && isInlineable(lhs) &&
                    (rhsSym is TACSymbol.Const || isInlineable(rhsSym as TACSymbol.Var))
                ) {
                    canBeReplacedWith[lhs] = rhsSym
                }
            }
        }
    }


    private fun go(): CoreTACProgram {
        for (b in g.blockIds) {
            processBlock(b)
        }
        logger.info {
            "Inlined $countReplacements variables, and removed $countRemovals self assignments"
        }
        // this is the only way I know to use a patching program and avoid type checking.
        val (newCode, blocks) = patcher.toCode(TACCmd.Simple.NopCmd)
        return code.copy(
            code = newCode,
            blockgraph = blocks,
        )
    }

    companion object {
        fun inlineAssignments(code: CoreTACProgram, isInlineable: (TACSymbol.Var) -> Boolean) =
            AssignmentInliner(code, isInlineable).go()
    }
}



