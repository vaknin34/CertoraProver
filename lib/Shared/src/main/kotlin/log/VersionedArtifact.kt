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

import java.io.File
import java.io.Serializable

/**
 * An artifact that may have different versions along a run of CVT.
 * [unversionedName] represents the name of the artifact, regardless of its version.
 * [versionedNameBuilder] should be used to generate the name of the artifact for a given version.
 *
 */
interface VersionedArtifact: Serializable {

    val unversionedName: String

    /**
     * (version) -> versionedName
     */
    val versionedNameBuilder: (Int) -> String

}

/**
 * A file that may be created in multiple versions along a run of CVT.
 */
class VersionedFile(filename: String) : VersionedArtifact {

    override val unversionedName: String = filename

    override val versionedNameBuilder: (Int) -> String
        get() = { version: Int ->
            File(unversionedName).let {
                "${it.nameWithoutExtension}_$version.${it.extension}"
            }
        }
}