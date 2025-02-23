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

package wasm.analysis.memory

import java.math.BigInteger

/*
 * An interface describing partition information for some target program
 * - if `permission(a)` is ReadWrite, then the program *may* write the address `a`
 * - if `permission(a)` is ReadOnly, then the program *must not* write the address `a`
 */
interface IMemoryPartitions {
    enum class Permission {
        ReadOnly,
        ReadWrite
        ;

        infix fun or(p: Permission): Permission =
            if (this == ReadWrite || p == ReadWrite) {
                ReadWrite
            } else {
                ReadOnly
            }
    }

    /**
     * @return [Permission.ReadOnly] if [ctp] *must not* write any address in [start, end]
     *         and [Permission.ReadWrite] otherwise
     */
    fun permission(start: BigInteger, end: BigInteger): Permission
}
