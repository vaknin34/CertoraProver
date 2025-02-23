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

package smt.axiomgenerators

/** Marks code that introduces overapproximations. When any of these marked places is visited, we should report the
 * overapproximation to the user.
 *
 * NB: I (alex n) am not sure yet what all these Target and Retention things mean -- I think we can adapt them as we go.
 *   Also not sure what's practical wrt. fields -- in the current form, this is just a humble beginning so we have some
 *   marker for these things.
 *   Thinking: we probably need to track them relative to each smt file in the end.. this marker might just remind us of
 *   that, if nothing else..
 */
@Target(AnnotationTarget.EXPRESSION)
@Retention(AnnotationRetention.SOURCE)
annotation class Overapproximation(val msg: String)
