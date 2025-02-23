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

import log.*
import org.apache.commons.lang3.SystemUtils
import kotlin.system.exitProcess


private val logger = Logger(LoggerTypes.COMMON)

class LongProcessKiller : Thread() {
    val frequencySeconds = 60
    override fun run() {

        while (true) {
            try {
                sleep(frequencySeconds.toLong() * 1000)
                if (SystemUtils.IS_OS_WINDOWS) {
                    /* This filter does not work for some reason in conjunction with /IM flag.
                        TODO: Run tasklist instead with the '/FI "IMAGENAME eq dot*"' flag instead, and parse PIDs. Kill each PID
                     */
                    val cmd = arrayOf("taskkill", "/F", "/FI", "CPUTIME ge 00:00:15", "/IM", "dot.exe", "/T")
                    logger.info{"Terminating all active dot processes: $cmd"}
                    Runtime.getRuntime().exec(cmd)
                } else if (SystemUtils.IS_OS_LINUX) {
                    val cmd = arrayOf("killall", "-o", "15s", "-f", "dot")
                    logger.info{"Terminating all active dot processes: $cmd"}
                    Runtime.getRuntime().exec(cmd)
                }
            } catch (e: InterruptedException) {
                return
            }
        }
    }

    fun bye() {
        try {
            this.interrupt()
        } catch (e: Exception) {
            try {
                Logger.alwaysError("Got error $e when interrupting")
            } catch (_: Exception) {
                // Logger.always exception can cause us to enter an infinite loop in EntryPoint
            }
            exitProcess(1)
        }
    }
}
