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

package spec

import config.Config.prependSourcesDir
import log.*
import utils.CertoraFileCache
import java.io.Reader
import java.io.StringReader

sealed class CVLSource {

    abstract val name: String
    abstract val origpath: String
    abstract fun getReader(): Reader
    abstract val isImported: Boolean

    data class File(val filepath: String, override val origpath: String, override val isImported: Boolean) :
        CVLSource() {
        override val name: String
            get() = filepath

        override fun getReader(): Reader = try {
            val path = prependSourcesDir(filepath)
            CertoraFileCache.getContentReader(path)
        } catch (e: Exception) {
            Logger.alwaysError("Could not access content of $origpath", e)
            throw e
        }
    }

    data class Raw(override val name: String, val rawTxt: String, override val isImported: Boolean) : CVLSource() {
        override val origpath: String
            get() = name

        override fun getReader(): Reader =
            StringReader(rawTxt)
    }
}
