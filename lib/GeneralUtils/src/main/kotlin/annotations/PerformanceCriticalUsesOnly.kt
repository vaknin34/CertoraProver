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

package annotations

/**
 * Indicates that the annotated API makes some "unsafe" tradeoffs to achieve better performance,
 * and thus should only be used when it has a significant, measurable, performance benefit,
 * and the safety tradeoffs are understood and accounted for.
 * 
 * It is a compile-time error to use such an API without a corresponding OptIn annotation, or a pass-through
 * PerformanceCriticalUsesOnly annotation.
 */
@RequiresOptIn(
    level = RequiresOptIn.Level.ERROR,
    message = "This API trades safety for performance; use only when there is a significant, measurable, performance benefit, and the safety tradeoffs are understood and accounted for.")
@Retention(AnnotationRetention.BINARY)
@Target(AnnotationTarget.CLASS, AnnotationTarget.FUNCTION)
annotation class PerformanceCriticalUsesOnly