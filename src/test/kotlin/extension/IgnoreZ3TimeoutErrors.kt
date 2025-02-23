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

import analysis.smtblaster.IBlaster
import org.junit.jupiter.api.extension.AfterAllCallback
import org.junit.jupiter.api.extension.BeforeAllCallback
import org.junit.jupiter.api.extension.ExtensionContext
import org.junit.jupiter.api.extension.TestExecutionExceptionHandler
import org.opentest4j.TestAbortedException
import java.util.concurrent.ExecutionException

class IgnoreZ3TimeoutErrors : TestExecutionExceptionHandler, BeforeAllCallback, AfterAllCallback {
    override fun handleTestExecutionException(context: ExtensionContext?, throwable: Throwable?) {
        if(isTimeoutException(throwable!!)) {
            throw TestAbortedException("Z3 timed-out")
        }
        throw throwable
    }

    private tailrec fun isTimeoutException(t: Throwable) : Boolean {
        return if(t is IBlaster.SmtTimeoutError) {
            true
        } else if(t is ExecutionException) {
            isTimeoutException(t.cause!!)
        } else if(t.cause != null) {
            isTimeoutException(t.cause!!)
        } else {
            false
        }
    }

    override fun beforeAll(context: ExtensionContext?) {
        IBlaster.FAIL_ON_TIMEOUT = true
    }

    override fun afterAll(context: ExtensionContext?) {
        IBlaster.FAIL_ON_TIMEOUT = false
    }
}