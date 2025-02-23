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

package analysis.pta

import com.certora.collect.*
import datastructures.stdcollections.*
import vc.data.TACKeyword
import vc.data.TACSymbol
import java.math.BigInteger

interface ConstVariableFinder {
    fun NumericDomain.variablesEqualTo(c: BigInteger) : Set<TACSymbol.Var> {
        val s = treapSetBuilderOf<TACSymbol.Var>()
        entries.mapNotNullTo(s) { (k, v) ->
            k.takeIf {
                /**
                 * See the comment in [IndexTracking.stepCommand] on why we're excluding the MEM* scalarized variables here.
                 */
                v is QualifiedInt && v.x.isConstant && v.x.c == c && it != TACKeyword.MEM0.toVar() && it != TACKeyword.MEM32.toVar()
            }
        }
        return s.build()
    }

    fun PointsToDomain.variablesEqualTo(c: BigInteger): Set<TACSymbol.Var> {
        return boundsAnalysis.variablesEqualTo(c)
    }
}
