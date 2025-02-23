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

package bridge

import datastructures.stdcollections.*
import kotlinx.serialization.Serializable
import spec.CVLInput
import spec.CVLSource
import java.nio.file.Path

/**
 * This class is a hot mess but we won't fix it... now.
 * From the times we really had no idea how to deal with serialization in kotlin (and it had bugs!)
 * It represents several kinds of possible verification query types.
 * - ASSERTION which is for the "assert"
 * - SPEC which is for the usual CVL checking
 * All require different kinds of fields. Marked
 */
@Serializable
data class VerificationQuery(
    val type: VerificationQueryType? = null,
    // for SPEC type:
    val primary_contract: String = "",
    val withInlining: Boolean = true,
    val specfile: String = "",
    val specfileOrigRelpath: String? = null,
    val specfilesToImportDecls: Map<String, List<String>>? = null,
    val importFilesToOrigRelpaths: Map<String, String>? = null,
    // for assertions:
    val primaryContracts: List<String>? = null,
) {

    fun toCVLInput(): CVLInput = if (specfilesToImportDecls != null && importFilesToOrigRelpaths != null) {
        CVLInput.WithImportedSpecs(
            CVLSource.File(specfile, specfileOrigRelpath ?: specfile, false),
            specfilesToImportDecls,
            importFilesToOrigRelpaths.map { (filepath, origpath) ->
                CVLSource.File(filepath, origpath, true)
            }
        )
    } else {
        CVLInput.Plain(CVLSource.File(specfile, specfileOrigRelpath ?: specfile, false))
    }

    /** for each stringified path in this query, resolve it with [base] as its new base dir */
    fun remapPaths(base: Path): VerificationQuery {
        fun remap(path: String): String = base.resolve(path).toString()

        return copy(
            specfile = remap(this.specfile),
            specfilesToImportDecls = this.specfilesToImportDecls?.mapKeys { (path, _) -> remap(path) },
            importFilesToOrigRelpaths = this.importFilesToOrigRelpaths?.mapKeys { (path, _) -> remap(path) },
        )
    }
}
