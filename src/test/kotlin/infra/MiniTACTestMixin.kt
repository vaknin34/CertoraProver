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

package infra

import java_cup.runtime.ComplexSymbolFactory
import utils.*
import vc.data.CoreTACProgram
import vc.data.minitac.MiniTACCmd
import vc.data.minitac.MiniTACCompiler
import vc.data.minitac.MiniTACLexer
import vc.data.minitac.MiniTACParser
import java.io.StringReader

interface MiniTACTestMixin {
    val handlers : Map<String, MiniTACCompiler.PluginHandler> get() = mapOf()

    fun loadMiniTAC(src: String): CoreTACProgram {
        val csf = ComplexSymbolFactory()
        val lexer = MiniTACLexer(csf, StringReader(src))
        val parser = MiniTACParser(lexer, csf)

        val prog : List<MiniTACCmd> = parser.parse().value.uncheckedAs()
        return MiniTACCompiler(prog, handlers)
    }
}
