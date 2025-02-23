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

package verifier

import analysis.maybeExpr
import datastructures.stdcollections.*
import log.*
import tac.MetaKey
import utils.mapNotNull
import vc.data.ConcurrentPatchingProgram
import vc.data.CoreTACProgram
import vc.data.TACExpr
import vc.data.tacexprutil.TACExprUtils.contains
import verifier.PolarityCalculator.Companion.POLARITY
import verifier.PolarityCalculator.Polarity
import verifier.PolarityCalculator.Polarity.NEG
import verifier.PolarityCalculator.Polarity.POS
import java.util.concurrent.atomic.AtomicInteger

val SKOLEM_VAR_NAME = MetaKey<String>("tac.skolem.var.name")

/**
 * Adds a [POLARITY] meta to quantified expressions. This is eventually used to replace `exists` quantifiers (or
 * equivalently, `forall` quantifiers in negative polarity) with skolem variables.
 */
class QuantifierAnnotator(val prog: CoreTACProgram) {
    private val concurrentPatcher = ConcurrentPatchingProgram(prog)
    private val polarityCalculator = PolarityCalculator(prog)

    companion object {
        private val skolemCounter = AtomicInteger(0)

        /** The meta is actually attached to the quantified variables */
        fun addPolarityMeta(expr: TACExpr, topPolarity: Polarity): TACExpr {
            return PolarityCalculator.transform(expr, topPolarity) { e, polarity ->
                if (e is TACExpr.QuantifiedFormula) {
                    e.copy(quantifiedVars = e.quantifiedVars.map { v ->
                        var meta = v.meta + (POLARITY to polarity)
                        if (e.isForall && polarity == NEG || !e.isForall && polarity == POS) {
                            meta += SKOLEM_VAR_NAME to "sklm!${v.namePrefix}!callId${v.callIndex}!${skolemCounter.incrementAndGet()}"
                        }
                        v.copy(meta = meta)
                    })
                } else {
                    e
                }
            }
        }
    }

    fun annotate(): CoreTACProgram {
        prog.parallelLtacStream()
            .mapNotNull { it.maybeExpr<TACExpr>() }
            .filter { lcmd -> lcmd.exp.contains { it is TACExpr.QuantifiedFormula } }
            .forEach { lcmd ->
                val p = polarityCalculator.polarityOfLhs(lcmd)
                if (p == null) {
                    Logger.Companion.alwaysWarn("Quantified cmd at ${lcmd.ptr} is not used and therefore dropped.")
                    concurrentPatcher.replace(lcmd.ptr, emptyList())
                } else {
                    concurrentPatcher.replace(
                        lcmd.ptr,
                        lcmd.cmd.copy(
                            rhs = addPolarityMeta(lcmd.exp, p)
                        )
                    )
                }
            }
        return concurrentPatcher.toCode()
    }
}
