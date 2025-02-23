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

package vc.data

import allocator.Allocator
import allocator.GeneratedBy
import com.certora.collect.*
import kotlinx.serialization.Serializable
import tac.Tag
import utils.*

/**
 * Define chceckpoint types.
 * TODO: we may prefer to move to sealed data classes for [VariableCheckpoint].
 */
enum class CheckpointType {
    GHOST
}

@Serializable
data class GenericSeries(
    @GeneratedBy(Allocator.Id.GHOST_CHECKPOINTS, source = true)
    override val id: Int,
    override val type: CheckpointType
) : VariableCheckpoint() {
    companion object {
        const val GENERIC_SERIES_NAME = "generic"
    }

    override val seriesName: String
        get() = GENERIC_SERIES_NAME

    override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): VariableCheckpoint {
        return this
    }

    override fun mapId(f: (Any, Int, () -> Int) -> Int): VariableCheckpoint {
        return GenericSeries(
            id = f(Allocator.Id.GHOST_CHECKPOINTS, id) { Allocator.getFreshId(Allocator.Id.GHOST_CHECKPOINTS) },
            type = type
        )
    }

    override fun hashCode(): Int {
        return hash {
            it + id + type
        }
    }
}

@Serializable
private data class VariableSeries(
    val v: TACSymbol.Var,
    override val type: CheckpointType
) : VariableCheckpoint() {
    override val seriesName: String
        get() = v.namePrefix

    override fun hashCode(): Int {
        return hash { it + v + type }
    }

    override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): VariableCheckpoint {
        return VariableSeries(
            v = f(v),
            type = type
        )
    }

    override fun mapId(f: (Any, Int, () -> Int) -> Int): VariableCheckpoint {
        return this
    }

    override val id: Int
        get() = 0
}

@Serializable
private data class NamedSeries(
    override val seriesName: String,
    override val type: CheckpointType
): VariableCheckpoint() {
    /*
    This is needed to make sure canonicalization (which has no notion of canonicalizing strings in meta)
    works with these named series. NB: This is no different from what we were actually doing before, where we just pretended
    the series was represented by a Bit256 (!!!) tagged variable.
     */
    override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): VariableCheckpoint {
        return NamedSeries(
            seriesName = f(TACSymbol.Var(seriesName, tag = Tag.BlockchainState)).namePrefix,
            type = type
        )
    }

    override fun mapId(f: (Any, Int, () -> Int) -> Int): VariableCheckpoint {
        return this
    }

    override val id: Int
        get() = 0

    override fun hashCode(): Int {
        return hash {
            it + seriesName + type
        }
    }
}

@KSerializable
@Treapable
sealed class VariableCheckpoint : TransformableVarEntity<VariableCheckpoint>, AmbiSerializable, UniqueIdEntity<VariableCheckpoint> {
    abstract val seriesName: String
    abstract val type : CheckpointType
    abstract val id: Int

    companion object {
        fun newGhostCheckpoint() =
            GenericSeries(Allocator.getFreshId(Allocator.Id.GHOST_CHECKPOINTS), type = CheckpointType.GHOST)

        fun ghostCheckpointByName(name: String): VariableCheckpoint {
            if (name == GenericSeries.GENERIC_SERIES_NAME) {
                throw CertoraInternalException(
                    CertoraInternalErrorType.GHOSTS,
                    "Ghost checkpoint series name must not be ${GenericSeries.GENERIC_SERIES_NAME}"
                )
            }
            return NamedSeries(name, CheckpointType.GHOST)
        }

        fun ghostCheckpointByVar(v: TACSymbol.Var): VariableCheckpoint {
            if (v.namePrefix == GenericSeries.GENERIC_SERIES_NAME) {
                throw CertoraInternalException(
                    CertoraInternalErrorType.GHOSTS,
                    "Ghost checkpoint series name must not be ${GenericSeries.GENERIC_SERIES_NAME}"
                )
            }
            return VariableSeries(v, CheckpointType.GHOST)
        }
    }
}
