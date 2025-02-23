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

package utils

/**
 * This is an alternative to @Deprecated, but it is flagged by detekt instead of the kotlin compiler.  This allows us
 * to use detekt's baseline feature to allow legacy uses of the class without disabling kotlin warnings.  See
 * [com.certora.detekt.Deprecation].
 *
 * Kotlin does not currently support fine-grained project-wide suppression of warnings; we either include -Werror or not.
 * See https://youtrack.jetbrains.com/issue/KT-8087
 *
 * Currently only deprecation of constructors is supported.
 */
annotation class DetektDeprecatedClass(
    val message: String
)
