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

package cache

/**
 * Caches a series of transformations until we see the pass name specified in the system property
 * cvt.force.pass. All future computations (including the named pass) are uncached.
 */
class UntilPassPolicy : CachePolicy {
    private val passName = System.getProperty("cvt.force.pass", "")
    override fun useCache(h: TransformationHistory): Boolean {
        return !h.contains(passName)
    }

    override fun useCache(load: ContractLoad): Boolean {
        return true
    }

}
