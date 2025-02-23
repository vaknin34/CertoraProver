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

package spec.cvlast

import com.certora.collect.*
import utils.*

@KSerializable
@Treapable
data class CVLStructPathNode(val rootStructType: CVLType.PureCVLType.Struct, val fields: List<CVLType.PureCVLType.Struct.StructEntry>) :
    AmbiSerializable {

    companion object {

        // StructPath(env, "msg", "sender") -> StructPath(env, ("msg", MSG), ("sender", address))
        // John's example should not break this :)))))

        operator fun invoke(rootStructType: CVLType.PureCVLType.Struct, vararg fields: String): CVLStructPathNode {
            val resolvedFields = mutableListOf<CVLType.PureCVLType.Struct.StructEntry>()
            var lastResolvedStructTypeField: CVLType.PureCVLType.Struct = rootStructType //Foo
            fields.forEachIndexed { idx, fieldName ->
                val resolvedField = lastResolvedStructTypeField.getEntryOrNull(fieldName)
                    ?: throw IllegalArgumentException(
                        "The fields: $fields do not describe a valid path" +
                                " that starts from the root struct type $rootStructType"
                    )
                resolvedFields.add(resolvedField)
                require(
                    (idx < (fields.size - 1) && resolvedField.cvlType is CVLType.PureCVLType.Struct) ||
                            (idx == (fields.size - 1) && resolvedField.cvlType !is CVLType.PureCVLType.Struct)
                ) { "Got an invalid path from struct type $rootStructType: $fields" }
                if (resolvedField.cvlType is CVLType.PureCVLType.Struct) {
                    lastResolvedStructTypeField = resolvedField.cvlType
                }
            }
            return CVLStructPathNode(rootStructType, resolvedFields)
        }
    }
}
