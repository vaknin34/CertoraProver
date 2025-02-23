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

package log

interface CategoryName {
    val name: String
}

interface LoggerName : CategoryName

val CategoryName.configName get() = name.lowercase().replace("_", ".")
fun CategoryName.withPrefix(prefix: String) = "$prefix.$configName"
fun LoggerName.toTopicProp(): String = withPrefix("topic")
fun LoggerName.toLevelProp(): String = withPrefix("level")
fun LoggerName.toVerboseProp(): String = withPrefix("verbose")
