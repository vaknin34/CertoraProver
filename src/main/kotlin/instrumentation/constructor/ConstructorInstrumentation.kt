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

package instrumentation.constructor

import analysis.EthereumVariables
import vc.data.CoreTACProgram
import vc.data.DefaultTACCmdMapper
import vc.data.TACMeta
import vc.data.TACSymbol
import datastructures.stdcollections.*
import java.math.BigInteger

object ConstructorInstrumentation {
    // adds a meta to variables that have the CODEDATA_KEY.
    // Should be applied only on TAC programs [c] coming from a constructor bytecode
    fun markConstructorCodeData(c: CoreTACProgram, hostAddres: BigInteger): CoreTACProgram {
        val constructorCodeDataSize = EthereumVariables.getConstructorCodeDataSize(hostAddres)
        val constructorCodeData = EthereumVariables.getConstructorCodeData(hostAddres)
        val toCtorCodeDataMapper = object : DefaultTACCmdMapper() {
            override fun mapVar(t: TACSymbol.Var): TACSymbol.Var {
                val codeDataKey = t.meta.get(TACMeta.CODEDATA_KEY)
                check(TACMeta.CONSTRUCTOR_CODE_KEY !in t.meta) {
                    "Apparently we have run this twice; existing reference $t to constructor data"
                }
                if(codeDataKey != null) {
                    check(codeDataKey == hostAddres) {
                        "Invariant broken, early in pipeline have disagreement about whose code this is $codeDataKey vs $hostAddres"
                    }
                    return constructorCodeData
                }
                val codeSizeKey = t.meta.get(TACMeta.CODESIZE_KEY) ?: return t
                check(codeSizeKey == hostAddres) {
                    "Invariant broken, early in pipeline have disagreement about whose code this is $codeSizeKey vs $hostAddres"
                }
                return constructorCodeDataSize
            }
        }
        return c.patching {
            it.addVarDecl(constructorCodeData)
            it.addVarDecl(constructorCodeDataSize)
            this.ltacStream().forEach { ltacCmd -> it.replaceCommand(ltacCmd.ptr, listOf(toCtorCodeDataMapper.map(ltacCmd.cmd))) }
        }
    }
}
