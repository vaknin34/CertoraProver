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

package loaders

import java.io.File
import java.io.InputStream

interface WithResourceFile {
    fun loadResourceFileOrCrash(path: String) : String {
        return this::class.java.classLoader.getResourceAsStream(path)?.bufferedReader()?.use {
            it.readText()
        } ?: error("$this: could not load resource")
    }

    fun loadResourceFile(path: String) : String? {
        return loadResourceFileAsStream(path).bufferedReader().use {
            it.readText()
        }
    }

    fun loadResourceFileAsStream(path: String): InputStream {
        return this::class.java.classLoader.getResourceAsStream(path)
    }

    fun resourceAsFile(path: String) =
        File(this::class.java.classLoader.getResource(path).toURI())
}
