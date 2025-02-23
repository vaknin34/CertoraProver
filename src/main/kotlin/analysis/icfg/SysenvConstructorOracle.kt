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

package analysis.icfg

import java.math.BigInteger

/**
 * For rapid testing. This allows you to pass bytecode strings and their resolution via sysenv
 * parameters, without having to re-run certoraRun.
 */
object SysenvConstructorOracle : IConstructorOracle {
    override fun resolve(m: Map<ScratchByteRange, BigInteger>): IConstructorOracle.PrototypeResolution? {
        val (sig, tgt) = System.getProperty("cvt.constructor")?.split(":", ignoreCase = false, limit = 2) ?: return null
        try {
            if (m.entries.singleOrNull()?.takeIf {
                it.key.from == BigInteger.ZERO
                }?.value == BigInteger(sig, 16)) {
                return IConstructorOracle.PrototypeResolution(BigInteger(tgt, 16), true)
            }
        } catch(_: Throwable) {}
        return null
    }
}