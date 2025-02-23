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

package analysis

import utils.monadicFold
import utils.monadicMap
import vc.data.TACSymbol

/**
 * The MustBeAnalysis class models the other MustBe* classes throughout the codebase but attempts to extend the
 * MustBe metaphor so that we can calculate "MustBeAnything." The class takes the same parameters as the other
 * MustBe classes:
 * @param graph the command graph
 * @param defAnalysis the define-analysis usually produced by NonTrivialDefAnalysis.
 */
open class MustBeAnalysis(private val graph: TACCommandGraph, private val defAnalysis: NonTrivialDefAnalysis) {

    /**
     * The mustBeAt function extends the MustBeSomethingAt metaphor to allow the programmer to give the function
     * a lambda that will verify that the object under consideration is a 'Something'.  If the object is a something
     * the function will call the second lambda to help with the fold in the monadicFold code.
     * @param where the pointer to the instruction
     * @param v the symbol defined at @e where.
     * @param checkIs the lambda that will verify that the LTACCmd under consideration is a 'Something'.  The lambda
     * should return the 'Something' when the LTACCmd is a 'Something' and null when the LTACCmd is not a
     * 'Something'.
     * @param collapser the lambda that the folder uses to change the list into a single value.
     * @return the object of type R if the object at is a 'Something' and null otherwise.
     */
    fun <R> mustBeAt(where: CmdPointer, v: TACSymbol.Var, checkIs: (LTACCmd) -> R?, collapser: (R, R) -> R?): R? {
        // The defAnalysis class has a method that searches for the definition location of the symbol 'v'.  See
        // the NonTrivialDefAnalysis class documentation(code) for a deeper understanding of 'non-trivial'. The
        // monadicMap code checks that wherever the TAC code actually defines 'v' in a 'non-trivial' way, that
        // the definition value is a 'Something' (R parameter).
        return defAnalysis.nontrivialDef(v, where).monadicMap {
            checkIs(graph.elab(it))
        }
            // Since we are checking across a list of values we fold the results into the actual value of
            // something in the monadicFold code, to assist we allow the user to provide a lambda that
            // that folds elements in the list.
            ?.monadicFold { a, b ->
                collapser(a, b)
            }
    }
}
