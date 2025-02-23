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

package smtlibutils.parser

object SmtSymbolQuoter {
    private val allowedSpecialChars =
        setOf('~', '!', '@', '$', '%', '^', '&', '*', '_', '-', '+', '=', '<', '>', '.', '?', '/')
    private val aToz: CharRange = 'a'..'z'
    private val AToZ: CharRange = 'A'..'Z'
    private val digits: CharRange = '0'..'9'
    private val reservedInitials = setOf('.', '@')
    private val reservedWords = setOf(
        "!",
        "_",
        "as",
        "BINARY",
        "DECIMAL",
        "exists",
        "HEXADECIMAL",
        "forall",
        "let",
        "match",
        "NUMERAL",
        "par",
        "STRING",
        "assert",
        "check-sat",
        "check-sat-assuming",
        "declare-const",
        "declare-datatype",
        "declare-datatypes",
        "declare-fun",
        "declare-sort",
        "define-fun",
        "define-fun-rec",
        "define-sort",
        "echo",
        "exit",
        "get-assertions",
        "get-assignment",
        "get-info",
        "get-model",
        "get-option",
        "get-proof",
        "get-unsat-assumptions",
        "get-unsat-core",
        "get-value",
        "pop",
        "push",
        "reset",
        "reset-assertions",
        "set-info",
        "set-logic",
        "set-option")

    /**
     * @return true iff `id` is a simple symbol in the sense of
     *     http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf
     */
    fun isSimpleSymbol(id: String): Boolean {
        if (id.isEmpty()) return false
        if (id[0] in digits) return false
        if (id[0] in reservedInitials) return false
        if (id in reservedWords) return false
        id.forEach { c ->
            when (c) {
                in allowedSpecialChars, in aToz, in AToZ, in digits -> Unit
                else -> return@isSimpleSymbol false
            }
        }
        return true
    }

    fun isQuoted(id: String) = id.length >= 3 && id[0] == '|' && id[id.length - 1] == '|'

    fun isValidSymbol(id: String) = isSimpleSymbol(id) || isQuoted(id)

    fun quoteIfNecessary(id: String): String = if (isValidSymbol(id)) id else quote(id)

    fun quote(id: String): String = "|$id|"
    fun unquote(id: String): String {
        check(isQuoted(id))
        return id.substring(1, id.length - 2)
    }

}