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

package json

import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.json.Json

object BasicJsonifier {
  /* print functions for key and value, default is toString */
  private fun valueToString(value: Any?, indent: Int): String =
      when (value) {
        is Set<*>,
        is List<*> ->
            (value as Collection<*>).joinToString(", ", "[", "]") { e -> valueToString(e, indent) }
        is Map<*, *> -> mapToJson(value, indent)
        is String -> Json.Default.encodeToString(String.serializer(), value)
        else -> value.toString()
      }

  fun <K, V> mapToJson(m: Map<K, V>, indent: Int = 0): String {
    val getTabs = { numTabs: Int -> "\n" + "\t".repeat(numTabs) }
    val postfix = getTabs(indent) + "}"
    val separator = "," + getTabs(indent + 1)
    val prefix = "{" + getTabs(indent + 1)
    return m.asSequence()
        .map { (key, value) ->
          valueToString(key, indent + 1) + ": " + valueToString(value, indent + 1)
        }
        .joinToString(separator = separator, prefix = prefix, postfix = postfix)
  }
}
