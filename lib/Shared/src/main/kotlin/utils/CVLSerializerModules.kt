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

import kotlinx.serialization.json.Json
import kotlinx.serialization.modules.*
import utils.*

/**
 * Collection of Kotlin polymorphic serializers for CVL ast elements.
 * These serializers are used, e.g.,
 *
 * 1. To dump [vc.data.TACProgram]s for caching using Java serialization.
 * If meta-maps contain [CVLType] values, Kotlin polymorphic serializers are required in case the underlying [CVLType] is
 * [SerializableWithAdapter].
 *
 * 2. To serialize the CVL ast into JSON format for the LSP.
 */
object CVLSerializerModules {
    val modules = serializersmodules.GeneralUtils + serializersmodules.Shared

    val format = Json {
        serializersModule = modules
    }
}
