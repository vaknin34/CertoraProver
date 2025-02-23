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

package os

import log.*
import utils.*
import java.lang.management.ManagementFactory
import java.nio.file.*

private val logger = Logger(GeneralUtilsLoggerTypes.SYSTEM)

fun dumpSystemConfig() {
    val os = ManagementFactory.getOperatingSystemMXBean()
    val runtime = ManagementFactory.getRuntimeMXBean()

    logger.info { "OS: ${os.getName()} ${os.getVersion()} ${os.getArch()}" }
    logger.info { "JVM: ${runtime.getVmName()} ${runtime.getVmVersion()}" }
    logger.info { "JVM args: ${runtime.getInputArguments()}"}

    if (os.getName() == "Linux") {
        logger.info { "vm.overcommit_memory: ${Files.readString(Path.of("/proc/sys/vm/overcommit_memory"))}" }
        logger.info {
            val cgroupMemLimitV1 = Path.of("/sys/fs/cgroup/memory/memory.limit_in_bytes")
            if (Files.exists(cgroupMemLimitV1)) {
                "cgroup memory limit (v1): ${Files.readString(cgroupMemLimitV1)}"
            } else {
                val cgroupMemLimitV2 = Path.of("/sys/fs/cgroup/memory.max")
                if (Files.exists(cgroupMemLimitV2)) {
                    "cgroup memory limit (v2): ${Files.readString(cgroupMemLimitV2)}"
                } else {
                    "cgroup memory limit: unknown"
                }
            }
        }
    }
}

