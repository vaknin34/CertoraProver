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

import tac.*

@Deprecated("Do not use this object anymore - tags should be explicitly given")
object TACUtils {
    fun tagsFromList(l: List<TACCmd>, tags: Tags.Builder<TACSymbol.Var>) {
        l.forEach { c ->
            tagsFromCommand(c, tags)
        }
    }

    fun tagsFromCommand(c: TACCmd.Simple): Tags<TACSymbol.Var> {
        val tags = tagsBuilder<TACSymbol.Var>()
        tagsFromCommand(c, tags)
        return tags.build()
    }

    fun tagsFromCommand(c: TACCmd, tags: Tags.Builder<TACSymbol.Var>) {
        c.getLhs()?.let {
            (it as? TACSymbol.Var)?.let {
                tags.safePut(it, it.tag)
            }
        }
        c.getFreeVarsOfRhs().forEach {
            tags.safePut(it, it.tag)
        }
        if (c is TACCmd.Simple.ByteLongCopy) { // TODO: can we update getFreeVarsOfRhs?
            tags.safePut(c.dstBase, c.dstBase.tag)
        }
    }

    fun tagsFromList(l: List<TACCmd>): Tags<TACSymbol.Var> {
        val tags = tagsBuilder<TACSymbol.Var>()
        tagsFromList(l, tags)
        return tags.build()
    }

    fun tagsFromBlocks(blocks: Map<NBId, List<TACCmd>>): Tags<TACSymbol.Var> {
        val tags = tagsBuilder<TACSymbol.Var>()
        blocks.forEach {
            tagsFromList(it.value, tags)
        }
        return tags.build()
    }
}