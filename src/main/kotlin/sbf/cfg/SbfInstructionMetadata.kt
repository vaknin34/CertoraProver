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

package sbf.cfg

import utils.*
import datastructures.stdcollections.*

class MetaData private constructor(private val meta: Map<MetaKey<*>, Any>) {
    constructor(): this(mutableMapOf())

    fun<T> getVal(key: MetaKey<T>): T? = meta[key]?.uncheckedAs()

    val keys: Collection<MetaKey<*>>
        get() = meta.keys

    operator fun<T> plus(entry: Pair<MetaKey<T>, T>): MetaData {
        return MetaData(meta.plus(entry.uncheckedAs<Pair<MetaKey<*>, Any>>()))
    }

    companion object {
        operator fun<T> invoke(entry: Pair<MetaKey<T>, T>): MetaData {
            return MetaData(mutableMapOf(entry.uncheckedAs()))
        }
    }
}

object SbfMeta {
    // These keys have relevant values
    val COMMENT = MetaKey<String>("comment")
    val CALL_ID = MetaKey<ULong>("callId")
    val INLINED_FUNCTION_NAME = MetaKey<String>("inlined.function")
    val KNOWN_ARITY = MetaKey<Int>("external.function.arity")
    val EQUALITY_REG_AND_STACK = MetaKey<Pair<Value.Reg, StackContentMeta>>("equality_reg_and_stack")
    val SBF_ADDRESS = MetaKey<ULong>("sbf_bytecode_address")
    // The value is true if the loaded register affects the control flow of the program
    val LOADED_AS_NUM_FOR_PTA = MetaKey<Boolean>("loaded_as_number_for_pta")
    //  Promoted overflow check condition
    val PROMOTED_ADD_WITH_OVERFLOW_CHECK = MetaKey<Condition>("promoted add.overflow check")
    // The MOV instruction sets the address of a global variable to a register
    val SET_GLOBAL = MetaKey<String>("set global")

    // These keys have empty strings as values. The values are irrelevant
    val HINT_OPTIMIZED_WIDE_STORE =  MetaKey<String>("hint.optimized_wide_store")
    val MEMCPY_PROMOTION = MetaKey<String>("promoted_stores_to_memcpy")
    val UNHOISTED_STORE = MetaKey<String>("unhoisted_store")
    val UNHOISTED_LOAD = MetaKey<String>("unhoisted_load")
    val UNHOISTED_MEMCPY = MetaKey<String>("unhoisted_memcpy")
    val UNHOISTED_MEMCMP = MetaKey<String>("unhoisted_memcmp")
    val UNHOISTED_STACK_POP = MetaKey<String>("unhoisted_stack_pop")
    val LOWERED_SELECT = MetaKey<String>("lowered_select")
    val REMOVED_MEMMOVE = MetaKey<String>("sol_memmove_")
    val LOWERED_ASSUME = MetaKey<String>("lowered_assume")
    val UNREACHABLE_FROM_COI = MetaKey<String>("unreachable_from_coi")
    val ADD_WITH_OVERFLOW = MetaKey<String>("add.overflow")
}

data class MetaKey<T>(val name: String)

data class StackContentMeta(val offset: Long, val width: Short)

fun toString(metaData: MetaData): String {
    val strB = StringBuilder()

    metaData.getVal(SbfMeta.COMMENT)?.let {
        strB.append(" /*$it*/")
    }
    for (k in metaData.keys) {
        when (k) {
            SbfMeta.HINT_OPTIMIZED_WIDE_STORE, SbfMeta.MEMCPY_PROMOTION,
            SbfMeta.UNHOISTED_STORE, SbfMeta.UNHOISTED_LOAD,
            SbfMeta.UNHOISTED_MEMCPY, SbfMeta.UNHOISTED_MEMCMP, SbfMeta.UNHOISTED_STACK_POP,
            SbfMeta.LOWERED_SELECT, SbfMeta.LOADED_AS_NUM_FOR_PTA, SbfMeta.REMOVED_MEMMOVE,
            SbfMeta.ADD_WITH_OVERFLOW, SbfMeta.SET_GLOBAL -> {
                strB.append(" /*${k.name}*/")
            }
            SbfMeta.CALL_ID -> {
                metaData.getVal(k)?.let {
                    strB.append(" /*callId=$it*/")
                }
            }
            SbfMeta.INLINED_FUNCTION_NAME -> {
                metaData.getVal(k)?.let {
                    strB.append(" /*inlined=$it*/")
                }
            }
            SbfMeta.SBF_ADDRESS-> {
                metaData.getVal(k)?.let {
                    val address: ULong = it.uncheckedAs()
                    strB.append(" /* 0x${address.toString(16)} */")
                }
            }
            SbfMeta.LOWERED_ASSUME -> {}
            SbfMeta.KNOWN_ARITY, SbfMeta.EQUALITY_REG_AND_STACK -> {}
            SbfMeta.UNREACHABLE_FROM_COI -> {}
            SbfMeta.COMMENT -> {}
            SbfMeta.PROMOTED_ADD_WITH_OVERFLOW_CHECK-> {
                metaData.getVal(k)?.let {
                    val cond: Condition = it.uncheckedAs()
                    strB.append(" /*${k.name}: $cond*/")
                }
            }
        }
    }
    return strB.toString()
}
