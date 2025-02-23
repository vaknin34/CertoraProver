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

package smt

import cli.ConversionException
import cli.Converter

enum class BackendStrategyEnum {
    ADAPTIVE,
    CEGAR,
    SINGLE_RACE,
}

val BackendStrategyEnumConverter = Converter {
    when (it.lowercase()){
        "adaptive" -> BackendStrategyEnum.ADAPTIVE
        "cegar" -> BackendStrategyEnum.CEGAR
        "singlerace" -> BackendStrategyEnum.SINGLE_RACE
        else -> throw ConversionException(it, BackendStrategyEnum::class.java)
    }
}
