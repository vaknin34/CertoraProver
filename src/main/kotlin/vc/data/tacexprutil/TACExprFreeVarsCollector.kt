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

package vc.data.tacexprutil

import analysis.storage.StorageAnalysisResult
import com.certora.collect.*
import tac.MetaKey
import tac.MetaMap
import utils.mapToTreapSet
import vc.data.TACExpr
import vc.data.TACMeta
import vc.data.TACSymbol
import java.io.Serializable

object TACExprFreeVarsCollector {
    private open class FreeVarCollectorBase : TACExprFolder<TreapSet<TACSymbol.Var>>() {
        override fun const(acc: TreapSet<TACSymbol.Var>, v: TACSymbol.Const): TreapSet<TACSymbol.Var> {
            return acc
        }

        override fun variable(acc: TreapSet<TACSymbol.Var>, v: TACSymbol.Var): TreapSet<TACSymbol.Var> {
            return acc + v
        }

        override fun mapDefinition(acc: TreapSet<TACSymbol.Var>, e: TACExpr.MapDefinition) =
            acc + (expr(treapSetOf(), e.definition) - e.defParams.map { it.s} )


        override fun quantifiedFormula(acc: TreapSet<TACSymbol.Var>, v: TACExpr.QuantifiedFormula) =
            acc + (expr(treapSetOf(), v.body) - v.quantifiedVars)
    }

    /** This does not collect variables appearing in metas and annotations */
    private val freeVarCollector = object : FreeVarCollectorBase() {
        override fun meta(acc: TreapSet<TACSymbol.Var>, m: MetaMap) =
            acc

        override fun <@Treapable R : Serializable> annotationExp(
            acc: TreapSet<TACSymbol.Var>,
            a: TACExpr.AnnotationExp<R>
        ) =
            expr(acc, a.o)
    }

    fun getFreeVars(e: TACExpr): TreapSet<TACSymbol.Var> = freeVarCollector.expr(treapSetOf(), e)
    fun getFreeVarsAsSyms(e: TACExpr): TreapSet<TACExpr.Sym.Var> = getFreeVars(e).mapToTreapSet { it.asSym() }


    /**
     * This collects some variables appearing in metas and annotations.
     * Currently only those appearing in [TACMeta.ACCESS_PATHS].
     * In general this is what should be used for cone-of-influence type optimizations.
     */
    private val freeVarCollectorExtended = object : FreeVarCollectorBase() {
        override fun <@Treapable R : Serializable> metaPair(acc: TreapSet<TACSymbol.Var>, k: MetaKey<R>, v: R) =
            if (k == TACMeta.ACCESS_PATHS) {
                acc + (v as StorageAnalysisResult.AccessPaths).support
            } else {
                super.metaPair(acc, k, v)
            }
    }

    fun getFreeVarsExtended(e: TACExpr): TreapSet<TACSymbol.Var> = freeVarCollectorExtended.expr(treapSetOf(), e)
}


fun TACExpr.getFreeVars(): Set<TACSymbol.Var> = TACExprFreeVarsCollector.getFreeVars(this)
fun TACExpr.getFreeVarsAsSyms(): Set<TACExpr.Sym.Var> = TACExprFreeVarsCollector.getFreeVarsAsSyms(this)
fun TACExpr.getFreeVarsExtended(): Set<TACSymbol.Var> = TACExprFreeVarsCollector.getFreeVarsExtended(this)




