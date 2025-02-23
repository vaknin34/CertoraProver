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

package cache.utils

import cache.SingletonCheckingStream
import cache.SubListAdaptingObjectOutput
import config.Config
import utils.uncheckedAs
import java.io.*
import java.util.zip.GZIPInputStream
import java.util.zip.GZIPOutputStream

object ObjectSerialization {

    private val inputStreamWrapper : (InputStream) -> InputStream = if(Config.FastCache.get()) {
        { stream: InputStream -> stream }
    } else {
        { stream: InputStream -> GZIPInputStream(stream) }
    }

    private val outputStreamWrapper : (OutputStream) -> OutputStream = if(Config.FastCache.get()) {
        { stream: OutputStream -> stream }
    } else {
        { stream: OutputStream -> GZIPOutputStream(stream) }
    }

    fun <T> writeObject(obj: T, filename: String) {
        BufferedOutputStream(FileOutputStream(filename)).use { stream ->
            writeObject(obj, stream)
        }
    }

    fun <T> writeObject(obj: T, output: OutputStream) {
        SubListAdaptingObjectOutput(outputStreamWrapper(output)).use {
            it.writeObject(obj)
        }
    }

    fun <T> readObject(file: File): T {
        return readObject(file.absolutePath)
    }

    fun <T> readObject(filename: String): T {
        return readObject(FileInputStream(filename))
    }

    fun <T> readObject(inputStream: InputStream): T {
        return SingletonCheckingStream(inputStreamWrapper(inputStream)).use { read ->
            val obj = read.readObject().uncheckedAs<T>()
            obj
        }
    }
}
