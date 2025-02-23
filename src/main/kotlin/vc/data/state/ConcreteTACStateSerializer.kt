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

package vc.data.state

import datastructures.Bijection
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.KSerializer
import kotlinx.serialization.builtins.MapSerializer
import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import log.Logger
import log.LoggerTypes
import vc.data.CoreTACProgram
import vc.data.TACSymbol

private val logger = Logger(LoggerTypes.TAC_INTERPRETER)

class ConcreteTACStateSerializer(
    val prog: CoreTACProgram,
    private val tacToCanonTable: Bijection<TACSymbol.Var, TACSymbol.Var>
) : KSerializer<ConcreteTACState> {

    override fun deserialize(decoder: Decoder): ConcreteTACState {
        val varNamesToValues = decoder.decodeSerializableValue(delegateMapSerializer)

        return ConcreteTACState(varNamesToValues.mapKeys { (vName, _) ->
            try {
                val v =
                    prog.symbolTable.nameToSymbol[tacToCanonTable.filterValues { canon -> canon.toString() == vName }
                        .keys.first().toString()] ?: error(
                        "Expected the variable $vName to be in the typescope of the program ${prog.name}"
                    )
                logger.debug { "FILE decoded v=$v" }
                tacToCanonTable[v]!!
            } catch (e: Exception) {
                logger.debug { "FILE-ERR v=$vName e=$e" }
                throw e
            }
        }.toMutableMap(), tacLockedVars = emptySet(), tacToCanonTable)
    }

    private val delegateMapSerializer = MapSerializer(String.serializer(), TACValue.serializer())
    @OptIn(ExperimentalSerializationApi::class)
    override val descriptor: SerialDescriptor = SerialDescriptor("ConcreteTACState", delegateMapSerializer.descriptor)

    override fun serialize(encoder: Encoder, value: ConcreteTACState) {
        val varNamesToValues: Map<String, TACValue> = value.initializedState().getMapFromVarNameToValue()
        encoder.encodeSerializableValue(delegateMapSerializer, varNamesToValues)
       // encoder.encodeSerializableValue(delegateSetSerializer, reachVars)
    }
}
