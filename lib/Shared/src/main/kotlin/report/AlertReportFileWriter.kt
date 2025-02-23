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

package report

import java.io.Closeable
import java.io.File
import java.io.RandomAccessFile

/**
 * a file writer which attempts to maintain the following invariant:
 * after every write, the file contents start with '[' and end with ']'.
 *
 * `file` is a path to a valid file. if the file doesn't exist, an attempt will be made to create it.
 *
 * if `append` is `false`, the file is truncated and initialized to valid (empty) array form.
 * otherwise, writes will append to the end of the file,
 * but in that case, it is required that the input file is already in array form (this is *not* validated)
 *
 * the mode used for [RandomAccessFile] is such that writes are synced to the storage
 * device immediately (in particular, no need for manual flushing)
 */
internal class AlertReportFileWriter(file: File, append: Boolean) : Closeable {
    private val raf: RandomAccessFile
    private var endPos: Long

    init {
        /** create file if it does not exist, sync writes to storage immediately on every update */
        val mode = "rws"

        raf = RandomAccessFile(file, mode)

        /**
         * while we don't validate array form in append mode, we do handle the trivial case where the file's too small.
         * this also ensures [endPos] > 0 at init,
         * so we won't later end up passing a negative value to [RandomAccessFile.seek]
         */
        val lengthAtInit = file.length()
        val emptyArray = "[]".toByteArray()

        endPos = if (append && lengthAtInit >= emptyArray.size) {
            raf.seek(lengthAtInit)
            lengthAtInit
        } else {
            raf.setLength(0)
            raf.write(emptyArray)
            emptyArray.size.toLong()
        }
    }

    fun write(s: String) {
        val bytes = s.toByteArray()

        if (bytes.isEmpty()) {
            return
        }

        /** seek back to overwrite array terminator */
        raf.seek(endPos - 1)

        raf.write(bytes)
        endPos += bytes.size

        /** we did not decrement [endPos] for the [RandomAccessFile.seek] call above, so no need to increment it here */
        raf.write(']'.code)
    }

    override fun close() {
        raf.close()
    }
}
