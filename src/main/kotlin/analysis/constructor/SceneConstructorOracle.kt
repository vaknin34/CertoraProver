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

package analysis.constructor

import analysis.icfg.IConstructorOracle
import analysis.icfg.ScratchByteRange
import normalizer.ConstructorBytecodeNormalizer
import scene.IContractClass
import scene.IContractWithSource
import scene.IScene
import utils.`to?`
import java.math.BigInteger

class SceneConstructorOracle(val scene: IScene) : IConstructorOracle, ConstructorBytecodeNormalizer {

    private val templates : List<Pair<BigInteger, String>> = scene.getContracts().mapNotNull {
        it.instanceId `to?` (it as? IContractWithSource)?.src?.constructorBytecode
    }.map { (addr, byteCode) ->
        addr to byteCode.stripCbor().sanitizeFinders()
    }

    override fun resolve(m: Map<ScratchByteRange, BigInteger>): IConstructorOracle.PrototypeResolution? {
        scene.getContracts().mapNotNull { it as? IContractWithSource }.singleOrNull {
            it.src.prototypeFor.any { proto ->
                /**
                 * Find the range that includes the constructor bytecode prefix...
                 */
                m.entries.singleOrNull {
                    it.key.from == BigInteger.ZERO
                }?.takeIf {
                    (it.key.to + BigInteger.ONE) >= (proto.length / 2).toBigInteger()
                }?.value?.let {
                    /**
                     * Does that prefix match this prototype?
                     */
                    it.toString(16).substring(proto.indices) == proto
                } == true
            }
        }?.let { return IConstructorOracle.PrototypeResolution((it as IContractClass).instanceId, true) } // if we found one, return now

        val mNormalized = m.mapValues { (k, v) ->
            val byteLength = (k.to - k.from).intValueExact() + 1
            /*
               why the zeropad? Because we're comparing strings generated from BigIntegers. If, for some totally
               bananas reason the BigInteger was equal to 2, but known to be taking up 3 bytes, then it's string
               representation should be 0000002, not 2 as would be returned by the toString method.
             */
            v.toString(16).zeroPadToBytes(byteLength).stripCbor().sanitizeFinders()
        }

        /**
         * For each such normalized constructor bytecode...
         */
        return templates.singleOrNull { (_, str) ->
            for((k, byteCodeFragment) in mNormalized) {
                if(str.extract(k) != byteCodeFragment) {
                    return@singleOrNull false
                }
            }
            true
        }?.first?.let {
            IConstructorOracle.PrototypeResolution(
                it, false
            )
        }
    }

    private fun String.extract(sb: ScratchByteRange): String? {
        val finalIndex = (sb.to.intValueExact() + 1) * 2
        if(finalIndex > this.length) {
            return null
        }
        return this.substring(sb.from.intValueExact() * 2, finalIndex)
    }

    private fun String.zeroPadToBytes(x: Int) : String {
        return if(this.length == x * 2) {
            this
        } else if(this.length > x * 2) {
            throw IllegalArgumentException("String is already too long")
        } else {
            this.padStart(x * 2, '0')
        }

    }


}