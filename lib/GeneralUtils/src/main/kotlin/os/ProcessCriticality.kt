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
import org.apache.commons.lang3.SystemUtils
import utils.*
import java.io.IOException
import java.nio.file.Files
import java.nio.file.Path

private val logger = Logger(GeneralUtilsLoggerTypes.SYSTEM)

/**
    Ensures that non-critical processes are killed first by the Linux OOM killer, so that critical processes are more
    likely to complete in the event of memory pressure.
 */
fun Process.setCriticality(critical: Boolean) {
    if (!critical && SystemUtils.IS_OS_LINUX) {
        // For non-critical processes, set oom_score_adj to the maximum value.  This ensures that such processes will be
        // among the first to be killed under memory exhaustion.
        try {
            logger.debug { "Raising OOM score of non-critical process ${this.pid()} $this" }
            Files.writeString(Path.of("/proc/${this.pid()}/oom_score_adj"), "1000")
        } catch (e: java.io.IOException) {
            logger.error { "Could not set OOM score adjustment for process ${this.pid()} ($this): $e" }
        }
    }
}

