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

package wasm.impCfg

import wasm.tokens.WasmTokens.BOTTOM

class TmpRefStackJoinError(message: String): Exception(message)

/*
* In the cfg, there is a mapping from pcs to instruction (and their succs).
* We want to make impcfg where we have mappings from pcs to blocks.
* We first do the translation such that we will an equivalent mapping from pcs to block cfgs that
* corresponds to the mapping from pcs to instructions.
* But we need to know what the stack looks like, for the translation to work.
*
* So at each PC, we will keep a stack of args (tmp variable names), such that
* the value of the tmp at the top of this stack will be whatever was at the top of the stack in the cfg, same
* for the second tmp, etc.
* We also want to know how a block changes the facts.
* */

sealed interface ArgStack {
    fun joinRefs(refB: ArgStack): ArgStack
    val size: Int?
}

data object Bottom: ArgStack {
    override val size = null

    override fun toString(): String {
        return BOTTOM
    }

    override fun joinRefs(refB: ArgStack): ArgStack {
        return refB
    }
}

data class RefStack(val args: List<Arg>): ArgStack {
    override val size = args.size

    override fun toString(): String {
        val stringOfRefs = args.joinToString(",") { it.toString() }
        return "RefStack [$stringOfRefs]"
    }

    override fun joinRefs(refB: ArgStack): ArgStack {
        if (refB is Bottom) {
            return this
        } else {
            val rsB = refB as RefStack
            if (this.args.size == rsB.args.size) {
                val aZipb = this.args.zip(rsB.args)
                return RefStack(aZipb.map { it.first.join(it.second) })
            } else {
                throw TmpRefStackJoinError("ArgStack.join: different ref stack lengths, A: ${this.args.size} and B: ${rsB.args.size}")
            }
        }
    }
}

/**
 * A StackFact is made out of two facts, the one at the entry, and one
 * at the exit. StackFacts are associated with PCs.
 * */
class StackFact(val entry: ArgStack, val exit: ArgStack) {
    override fun toString(): String {
        return "<$entry>\n <$exit>\n"
    }
}

