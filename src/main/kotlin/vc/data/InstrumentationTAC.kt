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

package vc.data

import com.certora.collect.*
import java.io.Serializable

interface InstrumentedTAC {
    val instrumentationTAC: InstrumentationTAC

}

/**
 * This class is meant to contain any TAC code that isn't strictly part of a program but may eventually
 * get instrumented (into the TAC program or the [LExpression] formulas).
 */
 @Treapable
data class InstrumentationTAC(
    val ufAxioms: UfAxioms,
): Serializable
