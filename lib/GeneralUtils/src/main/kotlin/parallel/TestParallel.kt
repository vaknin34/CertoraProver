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

package parallel

import utils.unused

@Suppress("SleepInsteadOfDelay")
fun main(args: Array<String>) {
    unused(args)
    ParallelPool().use { runPool ->
        val start = System.currentTimeMillis()
        val res = runPool.run {
            rpc {
                Thread.sleep(1000)
                3
            }.parallelBind(rpc {
                Thread.sleep(2000)
                5
            }) { a, b ->
                rpc {
                    Thread.sleep(1000)
                    a + 4 + b
                }
            }.bind { d ->
                complete(d)
            }
        }
        val end = System.currentTimeMillis()
        println(end - start)
        println(res)
    }
}
