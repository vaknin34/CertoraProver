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

package smtlibutils.cmdprocessor

/**
 * Holds an [SmtFormulaCheckerResult] and optionally the [SmtFormulaChecker] that was used to obtain it. This is meant
 * to be used within [LExpVcChecker], while the [SmtFormulaCheckerResult] is used outside of this as well.
 *
 * The idea is to remove the checker from the checker result eventually, to keep the checker more internal.
 */
data class SmtFormulaCheckerResultWithChecker(
    val checker: SmtFormulaChecker?,
    val result: SmtFormulaCheckerResult,
)

fun SmtFormulaCheckerResult.withChecker(checker: SmtFormulaChecker?) =
    SmtFormulaCheckerResultWithChecker(checker, this)
fun SmtFormulaCheckerResult.withNullChecker() =
    SmtFormulaCheckerResultWithChecker(null, this)

fun List<SmtFormulaCheckerResultWithChecker>.closeAll() {
    this.forEach { it.checker?.close() }
}
fun List<SmtFormulaCheckerResultWithChecker>.closeAllExcept(keepAliveId: Int) {
    this.forEachIndexed { id, res ->
        if (id != keepAliveId) {
            res.checker?.close()
        }
    }
}
