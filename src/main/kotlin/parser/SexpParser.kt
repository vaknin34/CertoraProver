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

package parser

import tac.Tag
import vc.data.*

sealed interface Sexpr {
    fun toEggTAC(type: Tag?): EggTAC

}

data class SAtom(val atom: String) : Sexpr {
    override fun toString(): String {
        return atom
    }

    override fun toEggTAC(type: Tag?): EggTAC {
        val num = atom.toBigIntegerOrNull()
        return if (num != null) {
            EggConst(num)
        } else if (type != null) {
            EggVar(atom, type)
        } else {
            error("$atom is not a valid Atom")
        }
    }


}


data class SList(val children: List<Sexpr>) : Sexpr {

    override fun toString(): String {
        return "(" + children.joinToString(" ") + ")"
    }

    override fun toEggTAC(type: Tag?): EggTAC {
        return when (children.size) {
            2 -> {
                EggUnary(children[0].toString(), children[1].toEggTAC(type))
            }
            3 -> {
                EggBinary(children[0].toString(), children[1].toEggTAC(type), children[2].toEggTAC(type))
            }
            else -> {
                error("toEggTAC: Cannot convert $this to a EggTAC")
            }
        }
    }

}

fun parseSexp(str: String, idx: Int): Pair<Sexpr, Int> {
    if (str[idx] == '(') {
        var next = idx + 1
        val elts = mutableListOf<Sexpr>()
        while (str[next] != ')') {
            val (elt, n) = parseSexp(str, next)
            next = n
            elts.add(elt)
        }
        if (str[next] == ')') {
            next += 1
        }
        return Pair(SList(elts), next)
    } else if (str[idx] == ' ') {
        return parseSexp(str, idx + 1)
    } else {
        val begin = idx
        var next = idx + 1
        while (next < str.length && str[next] != ' ') {
            if (str[next] == ')') {
                return Pair(SAtom(str.substring(begin, next)), next)
            }
            next += 1
        }
        val token = str.substring(begin, next)
        return Pair(SAtom(token), next)

    }
}

