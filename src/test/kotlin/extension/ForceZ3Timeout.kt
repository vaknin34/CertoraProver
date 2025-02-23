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

package extension

import analysis.smtblaster.Z3BlasterPool
import annotation.Z3Timeout
import org.junit.jupiter.api.extension.AfterAllCallback
import org.junit.jupiter.api.extension.BeforeAllCallback
import org.junit.jupiter.api.extension.ExtensionContext
import kotlin.time.Duration
import java.util.*
import kotlin.time.Duration.Companion.milliseconds

class ForceZ3Timeout : BeforeAllCallback, AfterAllCallback {
    override fun beforeAll(context: ExtensionContext?) {
        context?.element?.flatMap {
            Optional.ofNullable(it.getAnnotation(Z3Timeout::class.java))
        }?.ifPresent {
            Z3BlasterPool.FORCE_Z3_TIMEOUT = it.timeoutMs.milliseconds
        }
    }

    override fun afterAll(context: ExtensionContext?) {
        Z3BlasterPool.FORCE_Z3_TIMEOUT = null
    }

}
