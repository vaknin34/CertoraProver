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

package sbf.disassembler

typealias ElfAddress = Long

/** Begin utilities to manipulates bytes **/
// Converts the Byte into Int by filling with 0s the most 24 significant bits
fun zeroExtend(b: Byte): Int {
    return b.toInt().and(0xff)
}
/// Convert a Long into an array of bytes
///   LSB           MSB
/// bytes[0] ... bytes[7]
fun toBytes(x: Long): ByteArray {
    val bytes = ByteArray(8)
    var n = x
    var i = 0
    while (i < 8) {
        bytes[i] = n.toByte()
        n = n.shr(8)
        i++
    }
    return bytes
}
/// Convert an Int into an array of bytes
///   LSB           MSB
/// bytes[0] ... bytes[3]
fun toBytes(x: Int): ByteArray {
    val bytes = ByteArray(4)
    var n = x
    var i = 0
    while (i < 4) {
        bytes[i] = n.toByte()
        n = n.shr(8)
        i++
    }
    return bytes
}
// Convert an array of 4 bytes into an Int
//  LSB          MSB
// bytes[0] ... bytes[3]
fun toInt(bytes: ByteArray): Int {
    check(bytes.size == 4)
    var i = 0
    var res = 0
    while (i < bytes.size) {
        res += bytes[i] * (1.shl(i))
        i++
    }
    return res
}
// Convert an array of 8 bytes into a Long
//  LSB          MSB
// bytes[0] ... bytes[7]
fun toLong(bytes: ByteArray): Long {
    check(bytes.size == 8)
    var i = 0
    var res:Long = 0
    while (i < bytes.size) {
        res += bytes[i] * (1.shl(i))
        i++
    }
    return res
}
fun toString(bytes: ByteArray): String {
    var res = String()
    var i = 0
    while (i < bytes.size) {
        res += bytes[i].toString(16)
        i++
        if (i < bytes.size) {
            res += " "
        }
    }
    return res
}
/** End utilities to manipulates bytes **/

