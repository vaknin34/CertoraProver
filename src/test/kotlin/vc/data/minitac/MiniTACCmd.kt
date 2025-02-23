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

package vc.data.minitac

import vc.data.TACExpr
import vc.data.TACSymbol

/**
 * This is minitac, a very simple textual front end for tac programs.
 * The grammar of these program is as follows, where non-terminals are given in UPPERCASE
 *
 * PROGRAM ::= COMMAND+
 *
 * COMMAND ::= V = E;
 *          | if ( E ) { PROGRAM } else { PROGRAM }
 *          | while ( e ) { PROGRAM }
 *          | goto L;
 *          | L:
 *          | marker( MSG );
 *          | embed ?DATA? MSG;
 *  E ::= V
 *     | Add(E, E)
 *     | Lt(E, E)
 *     | *
 *     | N
 *  N ::= 0, 1, ...
 *  V ::= x, y, ...
 *  MSG ::= " ... "
 *  DATA ::= (see below)
 *
 * Minitac is untyped, and broadly unstructured: you can set up crazy jumping/looping behavior with unstructured `goto`
 * commands. The denotation of if/while/goto and assignments should be self-explanatory. `marker(...)` inserts an
 * annotation command with the [MiniTACCompiler.MARKER] payload as the literal string message.
 *
 * `embed` is the only exotic feature. It allows arbitrary code generation in the skeleton provided by
 * the [MiniTACCompiler]. The syntax for the command is the literal embed keyword, any amount of whitespace,
 * and then a single non-whitespace character. This character can be anything you want (but it is usually something
 * non-alphanumeric, like ! or @). This character is then taken to be the "delimiter" for the embedding. All characters
 * following this delimiter which are not the delimiter themselves are then collected into the "payload" for the embed statement.
 * For example, this is a valid embedding: embed @{"haha": 3}@ "hello"; which the eagle-eyed reader notes lets us embed
 * json into the program. Of course, because ! doesn't appear in the payload string, we could have used it as the delimiter as well.
 *
 * Following the second occurrence of the delimiter character, there can be any amount of whitespace, and then a string. This
 * string indicates the [vc.data.minitac.MiniTACCompiler.PluginHandler] which is used to translate the embed statement
 * into a sequence of tac commands.
 *
 * Finally a note on variables: all expressions and variables have [tac.Tag.Bit256] type, even `Lt` is actually compiled
 * to `Lt(a, b) ? 1 : 0`. This is to make the compilation process *waaay* easier.
 */
sealed interface MiniTACCmd {
    sealed interface WithExpressionCommand : MiniTACCmd {
        val expr: TACExpr
    }

    data class Assign(
        val lhs: TACSymbol.Var,
        val rhs: TACExpr
    ) : WithExpressionCommand {
        override val expr: TACExpr
            get() = rhs
    }

    data class LabelCmd(val label: String) : MiniTACCmd

    data class GotoCmd(val label: String) : MiniTACCmd

    data class Conditional(val cond: TACExpr, val thenBranch: List<MiniTACCmd>, val elseBranch: List<MiniTACCmd>?) : WithExpressionCommand {
        override val expr: TACExpr
            get() = cond
    }

    data class While(val cond: TACExpr, val body: List<MiniTACCmd>) : MiniTACCmd, WithExpressionCommand {
        override val expr: TACExpr
            get() = cond
    }

    data class Opaque(val handler: String, val payload: String) : MiniTACCmd

    data class Marker(val payload: String) : MiniTACCmd
}
