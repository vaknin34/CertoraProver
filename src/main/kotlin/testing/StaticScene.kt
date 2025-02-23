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

package testing

import java.math.BigInteger

fun String.asSource(solc: String = "solc", optimize: Boolean = false) = StaticContractSource(this, solc, BigInteger.ZERO, optimize)

private fun String?.toReturnsClause() = this?.let { "returns ($it)" } ?: ""

fun String.wrapInTrivialContract(returnType : String? = null) = this.wrap(returnType.toReturnsClause(), "")

private fun String.wrap(returnString: String, paramString: String) = """
 contract Test {
  function test($paramString) public $returnString {
     $this
  }
}
""".trimIndent()

fun String.wrapInTrivialContract(returnType: String? = null, vararg uintParams: String) = this.wrap(returnType.toReturnsClause(),
        uintParams.joinToString(",") { "uint $it" }
)
