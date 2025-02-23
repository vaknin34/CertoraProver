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

import config.Config
import config.SOURCES_SUBDIR
import java.io.*
import java.nio.file.Files
import java.nio.file.NoSuchFileException
import java.util.concurrent.ConcurrentHashMap
import kotlin.io.path.Path

class CertoraFileCacheException(override val cause: Exception, file: File) : Exception(
    "Failed to retrieve file: while attempting to cache $file, got exception: $cause"
)

/**
 * This class caches file content so that we do not have to access a file on the filesystem.
 * This is useful in the situation where we only have a run-repro.json file that contains a JSON
 * representation of the various .certora_* files, including files present in the .certora_config directory.
 */
object CertoraFileCache {

    private val fileToString = ConcurrentHashMap<CanonFile, String>()
    private val fileToBytes = ConcurrentHashMap<CanonFile, ByteArray>()
    private val fileToLineStarts = ConcurrentHashMap<CanonFile, LineStarts>()

    fun certoraSourcesDir(): File {
        val buildDir = Config.CertoraBuildDirectory.get()
        return File(buildDir).resolve(SOURCES_SUBDIR).normalize()
    }

    /**
     * XXX: we're handing out a [Reader] even though we cache the entire string.
     * maybe the users of this should be handling strings instead.
     */
    fun getContentReader(fileName: String): Reader {
        val content = stringContent(fileName)
        return StringReader(content)
    }

    fun stringContent(fileName: String): String {
        val canonFile = canonicalize(fileName)
        return fileToString.computeIfAbsent(canonFile) {
            /** if we ended up fetching the bytes from storage, we might as well cache them */
            val bytes = loadBytes(canonFile)

            /** this assumes UTF-8 */
            String(bytes)
        }
    }

    fun byteContent(fileName: String): ByteArray {
        val canonFile = canonicalize(fileName)
        return loadBytes(canonFile)
    }

    fun lineStarts(fileName: String): LineStarts {
        val canonFile = canonicalize(fileName)
        return fileToLineStarts.computeIfAbsent(canonFile) {
            val bytes = loadBytes(canonFile)
            LineStarts.fromBytes(bytes)
        }
    }

    private fun canonicalize(fileName: String): CanonFile {
        val readerPath = findReaderPath(fileName).ifEmpty { fileName }
        return CanonFile(readerPath)
    }

    // return the relative path from CERTORA_INTERNAL_ROOT, if there is not such path empty string is returned
    private fun findReaderPath(path: String): String {
        if (File(path).exists()) {
            return path
        }
        val index = path.indexOf(SOURCES_SUBDIR)
        var relPath = ""
        if (index >= 0) {
            relPath = path.substring(index)
            if (File(relPath).exists()) {
                return relPath
            }
            // There are cases where generated files that were generated during past builds are sent to the reader
            // these files will be under an old build directory that does not exist anymore, in these cases
            // we look for the file in the current build directory and return it
            val pathInBuild = Path(Config.CertoraBuildDirectory.get()).resolve(relPath).toString()
            if (File(pathInBuild).exists()) {
                return pathInBuild
            }
        }
        return relPath
    }

    /** read [canonFile] as bytes and cache the result, or fetch existing cache content if available */
    private fun loadBytes(canonFile: CanonFile): ByteArray = fileToBytes.computeIfAbsent(canonFile) {
        val file = canonFile.canon
        try {
            Files.readAllBytes(file.toPath())
        } catch (e: FileNotFoundException) {
            throw CertoraFileCacheException(e, file)
        } catch (e: NoSuchFileException) {
            throw CertoraFileCacheException(e, file)
        } catch (e: IOException) {
            throw CertoraFileCacheException(e, file)
        }
    }
}
